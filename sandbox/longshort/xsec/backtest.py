"""Cross-sectional ETF long/short: the same stack, run where breadth exists.

Run:  python3 -m xsec.backtest

The SPY book was not wrong, it was under-powered: at the Sharpe it produced,
reaching ``t = 2`` would have taken 505 years of daily data, and the placebo
put this pipeline's detection floor at Sharpe 0.44.  Nothing about a
single-asset daily direction forecast plausibly clears that.

The fundamental law of active management says ``IR ~ IC * sqrt(breadth)``, so
the only lever that changes the exponent is the number of independent bets per
period.  Going from one asset to a ~50-name cross-section multiplies the
detectable-effect scale by ``sqrt(50) ~ 7``, which turns 505 years into about
ten.  Everything else in the stack -- PIT, minimax shrinkage, Kelly, Hedge, the
execution band, and the whole audit layer -- is reused unchanged.

Timing contract is identical: ``pos[t]`` is set at the close of ``t`` from data
stamped ``<= t`` and earns ``r_fwd[t]``.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, asdict, replace

import numpy as np
import pandas as pd

from common import edge as edge_mod
from common import execution, game, pit
from common import stats as stats_mod
from xsec import features, universe

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")


@dataclass
class Config:
    min_history: int = 252          # trading days before an ETF becomes eligible
    min_names: int = 8              # smallest cross-section worth ranking
    mean_min_obs: int = 504         # 2y before an expert's mean is believed
    kappa: float = 1.0              # minimax shrinkage, in standard errors
    vol_halflife: float = 21.0
    # No fractional-Kelly constant here: the vol target sets the book's size,
    # so any constant multiple in front of the raw weights simply cancels.
    expert_cap: float = 6.0         # cap on each expert's Kelly multiple
    target_vol_ann: float = 0.10    # book risk budget; Sharpe is invariant to it
    gross_cap: float = 4.0          # backstop only -- should rarely bind
    cost_bps: float = 5.0           # ETFs are wider than SPY
    # Signal is read at the close of t and the trade goes on at the close of
    # t+1.  Executing at the *same* close is not implementable and, on a
    # universe full of international ETFs whose prices are hours stale by the
    # US close, it manufactures an enormous fake 1-day reversal edge.  Lag 0 is
    # reported as a diagnostic below, never as a result.
    impl_lag: int = 1
    hedge_eta_scale: float = 1.0
    bootstrap_draws: int = 2000
    block_length: float = 20.0
    placebo_draws: int = 200
    placebo_block: int = 63


# ---------------------------------------------------------------------------

def prepare(cfg: Config) -> dict:
    prices, rf, eligible = universe.load_prices(min_history=cfg.min_history)
    built = features.build(prices, rf, eligible, vol_halflife=cfg.vol_halflife)
    built["prices"] = prices
    built["eligible"] = eligible
    built["universe"] = universe.summary(prices, eligible)
    return built


def pipeline(prep: dict, r_fwd: pd.DataFrame, cfg: Config,
             full: bool = True) -> dict:
    """Everything downstream of the forward returns, so the placebo can re-run it."""
    names = features.EXPERTS
    dates = r_fwd.index
    T, K = len(dates), len(names)
    weights = prep["weights"]

    # Everything downstream learns from the payoff the book actually earns.
    # With an execution lag the score at t is traded at t+lag and earns
    # t+lag -> t+lag+1, so estimating on the *unlagged* return would tune the
    # book to a return stream it never collects -- and would read one day into
    # the future, since that payoff is not observable until t+1+lag.
    lag = cfg.impl_lag
    r_eff = r_fwd.shift(-lag) if lag else r_fwd
    r_mat = np.nan_to_num(r_eff.to_numpy())

    q = np.column_stack([
        (weights[k] * r_eff.fillna(0.0)).sum(axis=1).to_numpy() for k in names
    ])
    active = np.column_stack([
        (weights[k].abs().sum(axis=1) > 0).to_numpy() for k in names
    ])
    q = np.where(active, q, np.nan)

    f = np.zeros((T, K))
    mu_rob = np.full((T, K), np.nan)
    for i in range(K):
        _, _, shrunk = edge_mod.rolling_mean(q[:, i], min_obs=cfg.mean_min_obs,
                                             kappa=cfg.kappa, lag=1 + lag)
        mu_rob[:, i] = shrunk
        sd_q = _shift(edge_mod.ewma_vol(q[:, i], halflife=cfg.vol_halflife), lag)
        f[:, i] = np.clip(edge_mod.kelly_fraction(np.nan_to_num(shrunk), sd_q),
                          -cfg.expert_cap, cfg.expert_cap)

    expert_pnl = np.nan_to_num(
        np.vstack([np.zeros((1 + lag, K)), (f * q)[:-(1 + lag)]]))
    gain_scale = game.causal_gain_scale(expert_pnl)
    gains = game.normalise_gains(expert_pnl, scale=gain_scale)
    W = game.hedge_weights(gains, eta_scale=cfg.hedge_eta_scale)

    live = np.isfinite(mu_rob).any(axis=1) & np.isfinite(q).any(axis=1)
    start = int(np.argmax(live)) if live.any() else T

    vol = prep["vol"].to_numpy()
    combo_w = sum(weights[k].to_numpy() * (W[:, i] * f[:, i])[:, None]
                  for i, k in enumerate(names))
    combo_alpha = np.nansum(W * f * np.nan_to_num(mu_rob), axis=1)
    target, pos, bands, lam, cap_hit = _build_book(
        combo_w, combo_alpha, cfg, r_mat, vol, start, lag)

    def book(p: np.ndarray, cost_bps: float | None = None) -> tuple[np.ndarray, ...]:
        c = cfg.cost_bps if cost_bps is None else cost_bps
        turn = np.abs(np.diff(p, axis=0, prepend=np.zeros((1, p.shape[1])))).sum(axis=1)
        g = (p * r_mat).sum(axis=1)
        return g, g - turn * c / 1e4, turn

    g_net, net, turnover = book(pos)
    net_naive = book(target)[1]

    # The per-expert books are only needed for the candidate pool; the placebo
    # re-runs this function thousands of times and does not want them.
    expert_net = np.column_stack([
        book(_build_book(weights[k].to_numpy() * f[:, i][:, None],
                         f[:, i] * np.nan_to_num(mu_rob[:, i]),
                         cfg, r_mat, vol, start, lag)[1])[1]
        for i, k in enumerate(names)
    ]) if full else np.zeros((T, K))
    equal_net = book(_build_book(
        sum(weights[k].to_numpy() * f[:, i][:, None] for i, k in enumerate(names)) / K,
        (f * np.nan_to_num(mu_rob)).mean(axis=1), cfg, r_mat, vol, start, lag)[1])[1] \
        if full else np.zeros(T)

    return {"q": q, "f": f, "mu_rob": mu_rob, "W": W, "gains": gains,
            "target": target, "pos": pos, "bands": bands, "lam": lam,
            "cap_hit": cap_hit, "gross": g_net, "net": net,
            "turnover": turnover, "net_naive": net_naive,
            "expert_net": expert_net, "equal_net": equal_net,
            "start": start, "gross_exposure": np.abs(pos).sum(axis=1),
            "n_positions": (np.abs(pos) > 1e-6).sum(axis=1)}


def _shift(v: np.ndarray, lag: int) -> np.ndarray:
    """Delay a causal estimate by ``lag`` extra days."""
    return v if lag <= 0 else np.concatenate((np.full(lag, np.nan), v[:-lag]))


def _build_book(raw_w: np.ndarray, raw_alpha: np.ndarray, cfg: Config,
                r_mat: np.ndarray, vol: np.ndarray, start: int,
                lag: int = 0) -> tuple[np.ndarray, ...]:
    """Risk-budget, cap, then band a raw weight matrix into a tradeable book.

    Three steps, in the order that keeps each one's premise true:

    1. **Vol target.**  Scale to a fixed risk budget using a causal EWMA of the
       book's own *unscaled* return, so cross-asset correlation is measured
       rather than assumed away by a diagonal covariance.
    2. **Gross cap.**  A backstop, not a sizing rule.  When it binds every day
       -- as it did before the vol target was added -- the cap silently becomes
       the strategy and nothing downstream is an optimum of anything.
    3. **No-trade band**, with ``lambda`` backed out of this book's own forecast
       return and variance rather than inherited from the single-asset case.
    """
    T = len(raw_w)
    raw_w = np.asarray(raw_w, dtype=float).copy()
    raw_w[:start] = 0.0
    raw_book = (raw_w * r_mat).sum(axis=1)
    vol_raw = _shift(edge_mod.ewma_vol(raw_book), 1 + lag)
    target_vol = cfg.target_vol_ann / np.sqrt(252.0)
    with np.errstate(divide="ignore", invalid="ignore"):
        scale = np.where(np.isfinite(vol_raw) & (vol_raw > 0),
                         target_vol / vol_raw, 0.0)

    target = raw_w * scale[:, None]
    gross_raw = np.abs(target).sum(axis=1)
    cap_hit = gross_raw > cfg.gross_cap
    target = target * np.where(cap_hit, cfg.gross_cap / np.maximum(gross_raw, 1e-12),
                               1.0)[:, None]
    target[:start] = 0.0

    lam = execution.implied_risk_aversion(np.abs(raw_alpha * scale),
                                          np.full(T, target_vol ** 2))
    pos = np.zeros_like(target)
    bands = np.zeros_like(target)
    for j in range(target.shape[1]):
        h = execution.causal_halflife(target[:, j], min_obs=cfg.min_history)
        pos[:, j], bands[:, j] = execution.no_trade_band(
            target[:, j], vol[:, j], h, cfg.cost_bps, lam, cfg.gross_cap)
    pos[:start] = 0.0
    return target, pos, bands, lam, cap_hit


# ---------------------------------------------------------------------------

def placebo(prep: dict, cfg: Config, n_draws: int,
            seed: int = 11) -> dict[str, np.ndarray]:
    """Re-run the whole procedure against returns it cannot predict.

    The permutation is applied to **whole dates**, identically across every
    asset, so the cross-sectional correlation structure of a trading day
    survives intact and only the alignment between signal and outcome is
    destroyed.  A per-asset shuffle would have broken the correlations too and
    made the null far too easy to beat.
    """
    rng = np.random.default_rng(seed)
    r_fwd = prep["r_fwd"]
    n = len(r_fwd)
    sharpes = {"net": np.empty(n_draws), "gross": np.empty(n_draws)}
    for b in range(n_draws):
        n_blocks = int(np.ceil(n / cfg.placebo_block))
        starts = rng.integers(0, n, size=n_blocks)
        idx = (starts[:, None] + np.arange(cfg.placebo_block)[None, :]).ravel()[:n] % n
        shuffled = pd.DataFrame(r_fwd.to_numpy()[idx], index=r_fwd.index,
                                columns=r_fwd.columns)
        out = pipeline(prep, shuffled, cfg, full=False)
        for key in sharpes:
            r = out[key][out["start"]:]
            r = r[np.isfinite(r)]
            sd = r.std(ddof=1)
            sharpes[key][b] = r.mean() / sd * np.sqrt(252) if sd > 0 else 0.0
    return sharpes


# ---------------------------------------------------------------------------

def run(cfg: Config = Config()) -> dict:
    prep = prepare(cfg)
    names = features.EXPERTS
    dates = prep["r_fwd"].index
    out = pipeline(prep, prep["r_fwd"], cfg)
    start = out["start"]
    sl = slice(start, len(dates) - 1)
    net = out["net"]

    spy = prep["excess"]["SPY"].to_numpy()
    bh = np.nan_to_num(np.concatenate((spy[1:], [0.0])))

    candidates = {f"expert:{n}": out["expert_net"][sl, i] for i, n in enumerate(names)}
    candidates["combo:hedge"] = net[sl]
    candidates["combo:equal_weight"] = out["equal_net"][sl]

    res: dict = {"config": asdict(cfg), "universe": prep["universe"]}
    res["sample"] = {
        "first_signal_date": str(dates[start].date()),
        "last_date": str(dates[len(dates) - 2].date()),
        "n_days": int(len(dates) - 1 - start),
        "median_breadth": float(prep["breadth"][sl].median()),
        "median_names_held": float(np.median(out["n_positions"][sl])),
        "median_gross_exposure": float(np.median(out["gross_exposure"][sl])),
    }
    res["execution"] = {
        "median_band_over_position": float(np.nanmedian(
            (np.abs(out["bands"]) / np.abs(out["target"]).clip(1e-9))[sl]
            [np.abs(out["target"][sl]) > 1e-6])),
        "median_implied_lambda": float(np.nanmedian(out["lam"][sl])),
        "pct_days_gross_cap_binds": float(out["cap_hit"][sl].mean()),
        "turnover_naive": float(np.abs(np.diff(out["target"][sl], axis=0))
                                .sum() / (len(dates) - 1 - start) * 252),
        "turnover_banded": float(out["turnover"][sl].sum()
                                 / (len(dates) - 1 - start) * 252),
    }
    # Decisive test for stale-price artefacts: a signal that only works when
    # executed at the same close it was computed from is not a signal.
    for lag in (0, 2):
        lagged = pipeline(prep, prep["r_fwd"], replace(cfg, impl_lag=lag))
        res[f"implementation_lag_{lag}d"] = stats_mod.performance(
            lagged["net"][lagged["start"]:len(dates) - 1])
    res["strategy_net"] = stats_mod.performance(net[sl], out["gross_exposure"][sl])
    res["strategy_gross"] = stats_mod.performance(out["gross"][sl])
    res["strategy_no_band"] = stats_mod.performance(out["net_naive"][sl])
    res["equal_weight_combo"] = stats_mod.performance(out["equal_net"][sl])
    res["buy_and_hold"] = stats_mod.performance(bh[sl])
    res["experts"] = {n: stats_mod.performance(out["expert_net"][sl, i])
                      for i, n in enumerate(names)}
    res["mean_weights"] = {n: float(out["W"][sl, i].mean())
                           for i, n in enumerate(names)}
    res["pct_days_active"] = {
        n: float(np.mean(np.abs(np.nan_to_num(out["mu_rob"][sl, i])) > 0))
        for i, n in enumerate(names)}

    ic = prep["ic"].iloc[sl]
    res["information_coefficient"] = {
        n: {"mean_ic": float(ic[n].mean()),
            "ic_t_stat": float(ic[n].mean() / ic[n].std(ddof=1)
                               * np.sqrt(ic[n].notna().sum())),
            "ic_ir_ann": float(ic[n].mean() / ic[n].std(ddof=1) * np.sqrt(252))}
        for n in names}

    res["bootstrap"] = stats_mod.stationary_bootstrap_ci(
        net[sl], n_boot=cfg.bootstrap_draws, mean_block=cfg.block_length)
    res["reality_check"] = stats_mod.reality_check(
        candidates, n_boot=cfg.bootstrap_draws, mean_block=cfg.block_length)
    res["deflated_sharpe"] = {
        str(k): stats_mod.deflated_sharpe(net[sl], n_trials=k)
        for k in (len(candidates), 50, 200)}
    res["hedge_regret"] = game.realised_regret(out["gains"][sl], out["W"][sl])
    res["overlay"] = stats_mod.overlay(bh[sl], net[sl])
    res["subperiods"] = stats_mod.subperiods(
        dates[sl], net[sl], ["2005-01-01", "2010-01-01", "2015-01-01",
                             "2020-01-01"])
    # A modern-era holdout, reported on its own: the full-sample tests are
    # dominated by 1999-2005, and an edge that lives only in the first quarter
    # of the sample is a historical fact, not a strategy.
    holdout = pd.Series(net[sl], index=dates[sl]).loc["2010-01-01":]
    res["holdout_post_2010"] = {
        **stats_mod.performance(holdout.to_numpy()),
        **stats_mod.stationary_bootstrap_ci(holdout.to_numpy(),
                                            n_boot=cfg.bootstrap_draws,
                                            mean_block=cfg.block_length),
        "years": float(len(holdout) / 252),
    }
    res["cost_sensitivity"] = {
        f"{c}bps": stats_mod.performance(out["gross"][sl] - out["turnover"][sl] * c / 1e4)
        for c in (0.0, 2.0, 5.0, 10.0, 20.0, 40.0)}

    os.makedirs(OUT, exist_ok=True)
    if cfg.placebo_draws:
        draws = placebo(prep, cfg, cfg.placebo_draws)
        for key, label in (("net", "placebo"), ("gross", "placebo_gross")):
            s, obs = draws[key], res[f"strategy_{key}"]["sharpe"]
            res[label] = {
                "draws": int(cfg.placebo_draws), "mean_sharpe": float(s.mean()),
                "sd_sharpe": float(s.std(ddof=1)),
                "pct_95": float(np.percentile(s, 95)),
                "pct_99": float(np.percentile(s, 99)),
                "observed_sharpe": float(obs),
                "p_value": float((s >= obs).mean()),
            }
            np.save(os.path.join(OUT, f"placebo_sharpes_{key}.npy"), s)

    daily = pd.DataFrame({
        "net": net, "gross": out["gross"], "net_naive": out["net_naive"],
        "buy_hold": bh, "gross_exposure": out["gross_exposure"],
        "n_positions": out["n_positions"], "turnover": out["turnover"],
        "breadth": prep["breadth"].to_numpy(),
    }, index=dates)
    for i, n in enumerate(names):
        daily[f"w_{n}"] = out["W"][:, i]
        daily[f"ic_{n}"] = prep["ic"][n].to_numpy()
    daily = daily.iloc[sl]
    daily.to_csv(os.path.join(OUT, "daily.csv"))
    with open(os.path.join(OUT, "results.json"), "w") as fh:
        json.dump(res, fh, indent=2, default=float)
    return res


# ---------------------------------------------------------------------------

HEAD = ["sharpe", "ann_return", "ann_vol", "max_drawdown", "hit_rate"]


def _fmt(d: dict, keys: list[str]) -> str:
    def one(k: str) -> str:
        v = d.get(k)
        if v is None or (isinstance(v, float) and not np.isfinite(v)):
            return f"{k}=n/a"
        return f"{k}={v:+.3f}"
    return "  ".join(one(k) for k in keys)


def report(res: dict) -> None:
    s, u = res["sample"], res["universe"]
    print("=" * 78)
    print(f"Cross-sectional ETF long/short  |  {s['first_signal_date']} -> "
          f"{s['last_date']}  ({s['n_days']} days)")
    print(f"{u['n_tickers']} ETFs, causal entry, median breadth "
          f"{s['median_breadth']:.0f} names   "
          f"median gross exposure {s['median_gross_exposure']:.2f}x")
    print("=" * 78)

    print("\n-- headline ------------------------------------------------------")
    for label, key in [("strategy (net)", "strategy_net"),
                       ("strategy (gross)", "strategy_gross"),
                       ("no exec band (net)", "strategy_no_band"),
                       ("equal-weight combo", "equal_weight_combo"),
                       ("SPY buy & hold", "buy_and_hold")]:
        print(f"{label:20s} {_fmt(res[key], HEAD)}")

    e = res["execution"]
    print(f"{'execution':20s} band/position={e['median_band_over_position']:.2f}  "
          f"lambda={e['median_implied_lambda']:.4f}  "
          f"gross cap binds {e['pct_days_gross_cap_binds']:.0%} of days  "
          f"turnover {e['turnover_naive']:.0f}x -> {e['turnover_banded']:.0f}x/yr")
    print(f"{'implementation lag':20s} " + "  ".join(
        f"+{k}d SR={res[f'implementation_lag_{k}d']['sharpe']:+.3f}" for k in (0, 2))
          + f"   (headline uses +{res['config']['impl_lag']}d)")

    print("\n-- experts (each standalone, net) --------------------------------")
    print(f"{'':14s} {'sharpe':>8s} {'ann_ret':>8s} {'maxDD':>8s} "
          f"{'hedge_w':>8s} {'active':>7s} {'IC':>8s} {'IC t':>7s}")
    for name, perf in sorted(res["experts"].items(),
                             key=lambda kv: -(kv[1].get("sharpe") or -9)):
        ic = res["information_coefficient"][name]
        print(f"{name:14s} {perf['sharpe']:+8.3f} {perf['ann_return']:+8.3f} "
              f"{perf['max_drawdown']:+8.3f} {res['mean_weights'][name]:8.3f} "
              f"{res['pct_days_active'][name]:7.0%} {ic['mean_ic']:+8.4f} "
              f"{ic['ic_t_stat']:+7.2f}")

    print("\n-- does it survive the statistics? -------------------------------")
    b = res["bootstrap"]
    print(f"stationary bootstrap Sharpe  {b['sharpe']:+.2f}  "
          f"90% CI [{b['ci_lo_5']:+.2f}, {b['ci_hi_95']:+.2f}]  "
          f"P(SR<=0)={b['p_sharpe_le_0']:.3f}")
    rc = res["reality_check"]
    print(f"White reality check          best={rc['best']}  stat={rc['best_stat']:.2f}  "
          f"crit95={rc['critical_95']:.2f}  p={rc['p_value']:.3f}  "
          f"(M={rc['n_candidates']})")
    for k, d in res["deflated_sharpe"].items():
        print(f"deflated Sharpe (trials={k:>3s})  SR={d['sharpe_ann']:+.2f}  "
              f"E[max SR|H0]={d['expected_max_sharpe_ann_under_null']:+.2f}  "
              f"DSR={d['deflated_sharpe_prob']:.3f}")
    for label, tag in (("placebo", "net  "), ("placebo_gross", "gross")):
        if label not in res:
            continue
        p = res[label]
        print(f"placebo, {tag} ({p['draws']} draws)   observed SR="
              f"{p['observed_sharpe']:+.2f}  null mean={p['mean_sharpe']:+.2f} "
              f"sd={p['sd_sharpe']:.2f}  95th={p['pct_95']:+.2f}  "
              f"p={p['p_value']:.3f}")
    g = res["hedge_regret"]
    print(f"Hedge regret vs best expert  {g['regret']:.1f}  "
          f"bound={g['bound_sqrt_T_logN_over_2']:.1f}  "
          f"respected={g['bound_respected']}")

    o = res["overlay"]
    print("\n-- as an overlay on SPY ------------------------------------------")
    print(f"correlation to SPY  {o['correlation']:+.3f}   "
          f"alpha {o['alpha_ann']:+.2%}/yr  t={o['alpha_t']:+.2f}   "
          f"beta {o['beta']:+.3f}")
    for k, v in o["mixes"].items():
        print(f"  SPY + {k:>5s} x strategy   SR={v['sharpe']:+.3f}  "
              f"ann={v['ann_return']:+.2%}  dd={v['max_drawdown']:+.1%}")

    h = res.get("holdout_post_2010")
    if h:
        print(f"\n-- modern-era holdout (post-2010, {h['years']:.1f} years) "
              f"-----------------")
        print(f"net SR {h['sharpe']:+.3f}  90% CI [{h['ci_lo_5']:+.2f}, "
              f"{h['ci_hi_95']:+.2f}]  P(SR<=0)={h['p_sharpe_le_0']:.3f}  "
              f"ann={h['ann_return']:+.2%}")

    print("\n-- subperiods ----------------------------------------------------")
    for k, perf in res["subperiods"].items():
        print(f"{k:24s} SR={perf['sharpe']:+.2f}  ret={perf['ann_return']:+.1%}  "
              f"dd={perf['max_drawdown']:+.1%}")

    print("\n-- cost sensitivity ----------------------------------------------")
    for k, perf in res["cost_sensitivity"].items():
        print(f"{k:>7s}  SR={perf['sharpe']:+.2f}  ann={perf['ann_return']:+.2%}")
    print()


if __name__ == "__main__":
    report(run())
