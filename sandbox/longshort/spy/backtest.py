"""Walk-forward SPY long/short book: PIT -> edge -> Kelly -> Hedge -> band -> audit.

Run:  python3 backtest.py

Timing contract enforced throughout:  ``pos[t]`` is decided at the close of day
``t`` from information available at that close, and earns ``r_fwd[t]``, the
excess return from close ``t`` to close ``t+1``.  Every estimate feeding
``pos[t]`` -- PIT quantiles, regression slopes, volatility, Hedge weights,
holding horizon -- is built from data stamped ``<= t``.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, asdict

import numpy as np
import pandas as pd

from common import edge as edge_mod
from common import execution, game, pit
from common import stats as stats_mod
from spy import features

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")


@dataclass
class Config:
    pit_min_obs: int = 252          # 1y before a signal is allowed a quantile
    slope_min_obs: int = 504        # 2y of pairs before an edge is believed
    kappa: float = 1.0              # minimax shrinkage, in standard errors
    vol_halflife: float = 21.0
    kelly_fraction: float = 0.5     # half-Kelly on the aggregate
    expert_cap: float = 2.0
    position_cap: float = 1.5
    cost_bps: float = 2.0           # per unit of turnover, one way
    hedge_eta_scale: float = 1.0
    hedge_gain_scale: float = 0.02
    bootstrap_draws: int = 2000
    block_length: float = 20.0
    placebo_draws: int = 300
    placebo_block: int = 63


# ---------------------------------------------------------------------------
# stage 1 -- the expensive, return-independent part (PIT scores)
# ---------------------------------------------------------------------------

def prepare(cfg: Config) -> dict:
    panel = features.build_panel()
    names = features.EXPERTS
    T = len(panel)
    z = np.full((T, len(names)), np.nan)
    for i, name in enumerate(names):
        z[:, i] = pit.expanding_pit(panel[name].to_numpy(dtype=float),
                                    min_obs=cfg.pit_min_obs)
    return {"panel": panel, "names": names, "z": z,
            "excess": panel["excess"].to_numpy(dtype=float)}


# ---------------------------------------------------------------------------
# stage 2 -- everything downstream of the returns, so it can be re-run on a
#            permuted return series to build a placebo distribution
# ---------------------------------------------------------------------------

def pipeline(prep: dict, excess: np.ndarray, cfg: Config) -> dict:
    z, names = prep["z"], prep["names"]
    T, N = z.shape
    r_fwd = np.concatenate((excess[1:], [np.nan]))
    sd = edge_mod.ewma_vol(excess, halflife=cfg.vol_halflife)

    m = np.full((T, N), np.nan)
    f = np.zeros((T, N))
    beta_rob = np.full((T, N), np.nan)
    for i in range(N):
        _, _, shrunk = edge_mod.rolling_slope(
            z[:, i], r_fwd, min_obs=cfg.slope_min_obs, kappa=cfg.kappa
        )
        beta_rob[:, i] = shrunk
        m[:, i] = shrunk * z[:, i]
        f[:, i] = np.clip(
            edge_mod.kelly_fraction(np.nan_to_num(m[:, i]), sd),
            -cfg.expert_cap, cfg.expert_cap,
        )

    # Expert PnL *realised on day t* is f[t-1] * r_fwd[t-1]; known at close t.
    expert_pnl = np.nan_to_num(np.vstack([np.zeros(N), (f * r_fwd[:, None])[:-1]]))
    gains = game.normalise_gains(expert_pnl, scale=cfg.hedge_gain_scale)
    W = game.hedge_weights(gains, eta_scale=cfg.hedge_eta_scale)

    live = np.isfinite(r_fwd) & np.isfinite(sd) & np.isfinite(beta_rob).any(axis=1)
    start = int(np.argmax(live)) if live.any() else T

    def execute(raw: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        tgt = np.clip(cfg.kelly_fraction * raw, -cfg.position_cap, cfg.position_cap)
        tgt[:start] = 0.0
        h = execution.causal_halflife(tgt, min_obs=cfg.pit_min_obs)
        p, w = execution.no_trade_band(tgt, sd, h, cfg.cost_bps,
                                       cfg.kelly_fraction, cfg.position_cap)
        p[:start] = 0.0
        return tgt, p, w

    def book(p: np.ndarray, cost_bps: float | None = None) -> tuple[np.ndarray, ...]:
        c = cfg.cost_bps if cost_bps is None else cost_bps
        turn = np.abs(np.diff(p, prepend=0.0))
        g = p * np.nan_to_num(r_fwd)
        return g, g - turn * c / 1e4, turn

    target, pos, band = execute((W * f).sum(axis=1))
    horizon = execution.causal_halflife(target, min_obs=cfg.pit_min_obs)
    gross, net, turnover = book(pos)
    net_naive = book(target)[1]

    expert_pos = np.column_stack([execute(f[:, i])[1] for i in range(N)])
    expert_net = np.column_stack([book(expert_pos[:, i])[1] for i in range(N)])
    eq_pos = execute(f.mean(axis=1))[1]
    equal_net = book(eq_pos)[1]

    m_blend = np.nansum(W * np.nan_to_num(m), axis=1) * cfg.kelly_fraction

    return {
        "r_fwd": r_fwd, "sd": sd, "start": start, "W": W, "f": f,
        "beta_rob": beta_rob, "target": target, "pos": pos, "band": band,
        "horizon": horizon, "gross": gross, "net": net, "turnover": turnover,
        "net_naive": net_naive, "expert_net": expert_net, "equal_net": equal_net,
        "eq_pos": eq_pos, "m_blend": m_blend, "gains": gains,
        "buy_hold": np.where(np.isfinite(r_fwd), r_fwd, 0.0),
    }


# ---------------------------------------------------------------------------
# stage 3 -- placebo: the same search, run against returns it cannot predict
# ---------------------------------------------------------------------------

def block_permute(x: np.ndarray, block: int, rng: np.random.Generator) -> np.ndarray:
    """Circular block shuffle: keeps volatility clustering, kills alignment."""
    n = len(x)
    n_blocks = int(np.ceil(n / block))
    starts = rng.integers(0, n, size=n_blocks)
    idx = (starts[:, None] + np.arange(block)[None, :]).ravel()[:n] % n
    return x[idx]


def placebo(prep: dict, cfg: Config, n_draws: int, seed: int = 7) -> dict:
    """Re-run the whole pipeline on permuted returns.

    This is the strictest null available here: it does not test one strategy,
    it tests *the entire procedure* -- ten experts, the PIT layer, the slope
    search, Hedge's expert selection, Kelly sizing, the execution band -- against
    a market that by construction contains nothing for it to find.  Whatever
    Sharpe the procedure manufactures out of pure noise shows up in this
    distribution, so the real Sharpe has to beat it to mean anything.
    """
    rng = np.random.default_rng(seed)
    excess = prep["excess"]
    finite = np.isfinite(excess)
    sharpes = np.empty(n_draws)
    for b in range(n_draws):
        shuffled = excess.copy()
        shuffled[finite] = block_permute(excess[finite], cfg.placebo_block, rng)
        out = pipeline(prep, shuffled, cfg)
        sl = slice(out["start"], len(shuffled) - 1)
        r = out["net"][sl]
        r = r[np.isfinite(r)]
        sd = r.std(ddof=1)
        sharpes[b] = r.mean() / sd * np.sqrt(252) if sd > 0 else 0.0
    return {"draws": n_draws, "sharpes": sharpes}


# ---------------------------------------------------------------------------

def run(cfg: Config = Config()) -> dict:
    prep = prepare(cfg)
    panel, names = prep["panel"], prep["names"]
    dates = panel.index
    T, N = len(panel), len(names)

    out = pipeline(prep, prep["excess"], cfg)
    start = out["start"]
    sl = slice(start, T - 1)  # drop the final row: r_fwd is undefined there
    net, gross, pos = out["net"], out["gross"], out["pos"]

    pit_resid = pit.pit_residuals(out["r_fwd"], out["m_blend"], out["sd"])

    candidates = {f"expert:{n}": out["expert_net"][sl, i] for i, n in enumerate(names)}
    candidates["combo:hedge"] = net[sl]
    candidates["combo:equal_weight"] = out["equal_net"][sl]

    results: dict = {"config": asdict(cfg)}
    results["sample"] = {
        "first_signal_date": str(dates[start].date()),
        "last_date": str(dates[T - 2].date()),
        "n_days": int(T - 1 - start),
    }
    results["strategy_net"] = stats_mod.performance(net[sl], pos[sl])
    results["strategy_gross"] = stats_mod.performance(gross[sl], pos[sl])
    results["strategy_no_band"] = stats_mod.performance(out["net_naive"][sl],
                                                        out["target"][sl])
    results["equal_weight_combo"] = stats_mod.performance(out["equal_net"][sl],
                                                          out["eq_pos"][sl])
    results["buy_and_hold"] = stats_mod.performance(out["buy_hold"][sl])
    results["experts"] = {
        n: stats_mod.performance(out["expert_net"][sl, i]) for i, n in enumerate(names)
    }
    results["execution"] = {
        "median_band_halfwidth": float(np.nanmedian(out["band"][sl])),
        "median_holding_horizon_days": float(np.nanmedian(out["horizon"][sl])),
        "turnover_naive": float(np.abs(np.diff(out["target"][sl])).sum()
                                / (T - 1 - start) * 252),
        "turnover_banded": float(np.abs(np.diff(pos[sl])).sum()
                                 / (T - 1 - start) * 252),
    }

    results["bootstrap"] = stats_mod.stationary_bootstrap_ci(
        net[sl], n_boot=cfg.bootstrap_draws, mean_block=cfg.block_length)
    results["reality_check"] = stats_mod.reality_check(
        candidates, n_boot=cfg.bootstrap_draws, mean_block=cfg.block_length)
    results["deflated_sharpe"] = {
        str(k): stats_mod.deflated_sharpe(net[sl], n_trials=k)
        for k in (len(candidates), 50, 200)
    }
    results["calibration"] = stats_mod.calibration(pit_resid[sl])
    results["hedge_regret"] = game.realised_regret(out["gains"][sl], out["W"][sl])
    results["overlay"] = stats_mod.overlay(out["buy_hold"][sl], net[sl])
    results["subperiods"] = stats_mod.subperiods(
        dates[sl], net[sl], ["2000-01-01", "2010-01-01", "2020-01-01"])
    results["subperiods_buy_and_hold"] = stats_mod.subperiods(
        dates[sl], out["buy_hold"][sl], ["2000-01-01", "2010-01-01", "2020-01-01"])
    results["cost_sensitivity"] = {
        f"{c}bps": stats_mod.performance(gross[sl] - out["turnover"][sl] * c / 1e4)
        for c in (0.0, 1.0, 2.0, 5.0, 10.0, 20.0)
    }
    results["mean_weights"] = {n: float(out["W"][sl, i].mean())
                               for i, n in enumerate(names)}
    results["final_weights"] = {n: float(out["W"][T - 2, i])
                                for i, n in enumerate(names)}
    # Fraction of days an expert survived the minimax threshold at all.
    results["pct_days_active"] = {
        n: float(np.mean(np.abs(np.nan_to_num(out["beta_rob"][sl, i])) > 0))
        for i, n in enumerate(names)
    }

    if cfg.placebo_draws:
        pl = placebo(prep, cfg, cfg.placebo_draws)
        s = pl["sharpes"]
        observed = results["strategy_net"]["sharpe"]
        results["placebo"] = {
            "draws": int(pl["draws"]),
            "mean_sharpe": float(s.mean()),
            "sd_sharpe": float(s.std(ddof=1)),
            "pct_95": float(np.percentile(s, 95)),
            "pct_99": float(np.percentile(s, 99)),
            "observed_sharpe": float(observed),
            "p_value": float((s >= observed).mean()),
        }

    daily = pd.DataFrame(
        {k: out[k] for k in ("target", "pos", "band", "horizon", "sd",
                             "gross", "net", "buy_hold", "m_blend")},
        index=dates,
    )
    daily["px"] = panel["px"]
    daily["pit"] = pit_resid
    for i, n in enumerate(names):
        daily[f"w_{n}"] = out["W"][:, i]
    daily = daily.iloc[start:T - 1]

    os.makedirs(OUT, exist_ok=True)
    daily.to_csv(os.path.join(OUT, "daily.csv"))
    if "placebo" in results:
        np.save(os.path.join(OUT, "placebo_sharpes.npy"), pl["sharpes"])
    with open(os.path.join(OUT, "results.json"), "w") as fh:
        json.dump(results, fh, indent=2, default=float)
    return results


# ---------------------------------------------------------------------------

def _fmt(d: dict, keys: list[str]) -> str:
    def one(k: str) -> str:
        v = d.get(k)
        if v is None or (isinstance(v, float) and not np.isfinite(v)):
            return f"{k}=n/a"
        return f"{k}={int(v)}" if k == "n_days" else f"{k}={v:+.3f}"
    return "  ".join(one(k) for k in keys)


HEAD = ["sharpe", "ann_return", "ann_vol", "max_drawdown", "hit_rate"]


def report(res: dict) -> None:
    s = res["sample"]
    print("=" * 78)
    print(f"SPY long/short  |  {s['first_signal_date']} -> {s['last_date']}  "
          f"({s['n_days']} trading days)")
    print("=" * 78)

    print("\n-- headline ------------------------------------------------------")
    for label, key in [("strategy (net)", "strategy_net"),
                       ("strategy (gross)", "strategy_gross"),
                       ("no exec band (net)", "strategy_no_band"),
                       ("equal-weight combo", "equal_weight_combo"),
                       ("SPY buy & hold", "buy_and_hold")]:
        print(f"{label:20s} {_fmt(res[key], HEAD)}")
    n = res["strategy_net"]
    print(f"{'positioning':20s} avg={n['avg_position']:+.2f}  "
          f"avg|pos|={n['avg_abs_position']:.2f}  "
          f"long {n['pct_long']:.0%} / short {n['pct_short']:.0%}  "
          f"turnover={n['ann_turnover']:.1f}x/yr")
    e = res["execution"]
    print(f"{'execution band':20s} halfwidth={e['median_band_halfwidth']:.2f}  "
          f"holding horizon={e['median_holding_horizon_days']:.0f}d  "
          f"turnover {e['turnover_naive']:.0f}x -> {e['turnover_banded']:.0f}x/yr")

    print("\n-- experts (each standalone, net) --------------------------------")
    for name, perf in sorted(res["experts"].items(),
                             key=lambda kv: -(kv[1].get("sharpe") or -9)):
        print(f"{name:14s} {_fmt(perf, ['sharpe', 'ann_return', 'max_drawdown'])}"
              f"  hedge_w={res['mean_weights'][name]:.3f}"
              f"  active={res['pct_days_active'][name]:.0%}")

    print("\n-- does it survive the statistics? -------------------------------")
    b = res["bootstrap"]
    print(f"stationary bootstrap Sharpe  {b['sharpe']:+.2f}  "
          f"90% CI [{b['ci_lo_5']:+.2f}, {b['ci_hi_95']:+.2f}]  "
          f"P(SR<=0)={b['p_sharpe_le_0']:.3f}")
    rc = res["reality_check"]
    print(f"White reality check          best={rc['best']}  "
          f"stat={rc['best_stat']:.2f}  crit95={rc['critical_95']:.2f}  "
          f"p={rc['p_value']:.3f}  (M={rc['n_candidates']})")
    for k, d in res["deflated_sharpe"].items():
        print(f"deflated Sharpe (trials={k:>3s})  SR={d['sharpe_ann']:+.2f}  "
              f"E[max SR|H0]={d['expected_max_sharpe_ann_under_null']:+.2f}  "
              f"DSR={d['deflated_sharpe_prob']:.3f}")
    if "placebo" in res:
        p = res["placebo"]
        print(f"placebo (whole pipeline on   observed SR={p['observed_sharpe']:+.2f}  "
              f"null mean={p['mean_sharpe']:+.2f} sd={p['sd_sharpe']:.2f}  "
              f"95th={p['pct_95']:+.2f}")
        print(f"  block-permuted returns)    p={p['p_value']:.3f}  "
              f"({p['draws']} draws)")
    c = res["calibration"]
    print(f"PIT calibration              KS={c['ks_stat']:.4f}  "
          f"p={c['ks_pvalue']:.3f}  mean={c['mean']:.3f}  "
          f"tail mass(5%)={c['tail_mass_5pct']:.3f} (want 0.100)")
    g = res["hedge_regret"]
    print(f"Hedge regret vs best expert  {g['regret']:.1f}  "
          f"bound sqrt(T lnN/2)={g['bound_sqrt_T_logN_over_2']:.1f}  "
          f"respected={g['bound_respected']}")

    o = res["overlay"]
    print("\n-- is it worth anything as an overlay on SPY? --------------------")
    print(f"correlation to SPY  {o['correlation']:+.3f}   "
          f"alpha t-stat {o['alpha_t']:+.2f}   beta {o['beta']:+.3f}")
    for k, v in o["mixes"].items():
        print(f"  SPY + {k:>5s} x strategy   SR={v['sharpe']:+.3f}  "
              f"ann={v['ann_return']:+.2%}  dd={v['max_drawdown']:+.1%}")

    print("\n-- subperiods (net vs buy & hold) --------------------------------")
    for k, perf in res["subperiods"].items():
        bh = res["subperiods_buy_and_hold"].get(k, {})
        print(f"{k:24s} SR={perf['sharpe']:+.2f}  ret={perf['ann_return']:+.1%}  "
              f"dd={perf['max_drawdown']:+.1%}   |  "
              f"B&H SR={bh.get('sharpe', float('nan')):+.2f}  "
              f"dd={bh.get('max_drawdown', float('nan')):+.1%}")

    print("\n-- cost sensitivity ----------------------------------------------")
    for k, perf in res["cost_sensitivity"].items():
        print(f"{k:>7s}  SR={perf['sharpe']:+.2f}  ann={perf['ann_return']:+.2%}")
    print()


if __name__ == "__main__":
    report(run())
