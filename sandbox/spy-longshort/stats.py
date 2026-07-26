"""The statistics layer -- almost entirely devoted to trying to kill the result.

A backtest's Sharpe ratio is a number you obtained by looking; the question is
always what that number would have been had you looked at pure noise the same
number of times.  Three separate attacks are implemented here:

* :func:`stationary_bootstrap_ci` -- a Politis-Romano block bootstrap gives a
  confidence interval that survives autocorrelation and volatility clustering,
  which the textbook ``SR * sqrt(T)`` t-statistic does not.
* :func:`reality_check` -- White's Reality Check.  The null is "the *best* of
  the M things I tried has no edge", so the sampling distribution is that of a
  maximum, not of a single mean.  This is the honest p-value for a strategy
  that was selected.
* :func:`deflated_sharpe` -- Bailey & Lopez de Prado's DSR, which corrects the
  Sharpe ratio for the number of trials *and* for non-normality of returns.

:func:`calibration` closes the PIT loop: it asks whether the predictive
distribution the strategy is actually betting through is the right one.
"""

from __future__ import annotations

import numpy as np
from scipy.stats import kstest, norm

ANN = 252.0
EULER = 0.5772156649015329


def performance(r: np.ndarray, positions: np.ndarray | None = None) -> dict:
    r = np.asarray(r, dtype=float)
    r = r[np.isfinite(r)]
    if len(r) < 2:
        return {}
    mu, sd = r.mean(), r.std(ddof=1)
    equity = np.cumprod(1.0 + r)
    peak = np.maximum.accumulate(equity)
    dd = equity / peak - 1.0
    ann_ret = mu * ANN
    ann_vol = sd * np.sqrt(ANN)
    out = {
        "n_days": len(r),
        "ann_return": ann_ret,
        "ann_vol": ann_vol,
        "sharpe": ann_ret / ann_vol if ann_vol > 0 else np.nan,
        "max_drawdown": dd.min(),
        "calmar": ann_ret / abs(dd.min()) if dd.min() < 0 else np.nan,
        "hit_rate": float((r > 0).mean()),
        "skew": float(((r - mu) ** 3).mean() / sd**3),
        "kurtosis": float(((r - mu) ** 4).mean() / sd**4),
        "t_stat": mu / sd * np.sqrt(len(r)),
        "total_return": float(equity[-1] - 1.0),
    }
    if positions is not None:
        p = np.asarray(positions, dtype=float)
        p = np.nan_to_num(p[-len(r):])
        out["avg_position"] = float(p.mean())
        out["avg_abs_position"] = float(np.abs(p).mean())
        out["ann_turnover"] = float(np.abs(np.diff(p)).sum() / len(p) * ANN)
        out["pct_long"] = float((p > 0).mean())
        out["pct_short"] = float((p < 0).mean())
    return out


def _stationary_bootstrap_index(n: int, mean_block: float,
                                rng: np.random.Generator) -> np.ndarray:
    p = 1.0 / mean_block
    idx = np.empty(n, dtype=int)
    i = rng.integers(0, n)
    for t in range(n):
        idx[t] = i
        if rng.random() < p:
            i = rng.integers(0, n)
        else:
            i = (i + 1) % n
    return idx


def stationary_bootstrap_ci(r: np.ndarray, n_boot: int = 2000,
                            mean_block: float = 20.0, seed: int = 0) -> dict:
    """Bootstrap CI for the annualised Sharpe ratio under serial dependence."""
    r = np.asarray(r, dtype=float)
    r = r[np.isfinite(r)]
    rng = np.random.default_rng(seed)
    sharpes = np.empty(n_boot)
    for b in range(n_boot):
        sample = r[_stationary_bootstrap_index(len(r), mean_block, rng)]
        sd = sample.std(ddof=1)
        sharpes[b] = sample.mean() / sd * np.sqrt(ANN) if sd > 0 else 0.0
    point = r.mean() / r.std(ddof=1) * np.sqrt(ANN)
    return {
        "sharpe": float(point),
        "ci_lo_5": float(np.percentile(sharpes, 5)),
        "ci_hi_95": float(np.percentile(sharpes, 95)),
        "p_sharpe_le_0": float((sharpes <= 0).mean()),
    }


def reality_check(candidates: dict[str, np.ndarray], n_boot: int = 2000,
                  mean_block: float = 20.0, seed: int = 0) -> dict:
    """White's Reality Check over the whole pool of things that were tried.

    ``H0``: none of the candidates has a positive expected return.  The test
    statistic is the maximum studentised mean, and the bootstrap distribution
    is built from *recentred* resamples, so the p-value already pays for the
    search across ``M`` candidates.
    """
    names = list(candidates)
    mat = np.column_stack([candidates[k] for k in names])
    mask = np.isfinite(mat).all(axis=1)
    mat = mat[mask]
    T, M = mat.shape
    mu = mat.mean(axis=0)
    sd = mat.std(axis=0, ddof=1)
    sd[sd == 0] = np.inf
    stat = np.sqrt(T) * (mu / sd)
    v_obs = stat.max()

    rng = np.random.default_rng(seed)
    v_boot = np.empty(n_boot)
    for b in range(n_boot):
        idx = _stationary_bootstrap_index(T, mean_block, rng)
        sample = mat[idx]
        v_boot[b] = (np.sqrt(T) * (sample.mean(axis=0) - mu) / sd).max()

    return {
        "n_candidates": M,
        "best": names[int(stat.argmax())],
        "best_stat": float(v_obs),
        "p_value": float((v_boot >= v_obs).mean()),
        "critical_95": float(np.percentile(v_boot, 95)),
    }


def deflated_sharpe(r: np.ndarray, n_trials: int,
                    sharpe_variance: float | None = None) -> dict:
    """Deflated Sharpe Ratio (Bailey & Lopez de Prado 2014).

    ``n_trials`` is how many strategy variants were evaluated to produce this
    one.  Under the null of zero true edge, the *expected maximum* Sharpe over
    that many trials is strictly positive -- DSR is the probability the observed
    Sharpe beats that selection-inflated benchmark.
    """
    r = np.asarray(r, dtype=float)
    r = r[np.isfinite(r)]
    T = len(r)
    mu, sd = r.mean(), r.std(ddof=1)
    sr = mu / sd  # per-period, not annualised
    skew = float(((r - mu) ** 3).mean() / sd**3)
    kurt = float(((r - mu) ** 4).mean() / sd**4)

    if sharpe_variance is None:  # variance of SR across trials, default = i.i.d.
        sharpe_variance = 1.0 / T
    sigma_sr = np.sqrt(sharpe_variance)
    n = max(n_trials, 2)
    sr0 = sigma_sr * (
        (1 - EULER) * norm.ppf(1 - 1.0 / n) + EULER * norm.ppf(1 - 1.0 / (n * np.e))
    )
    denom = np.sqrt(max(1 - skew * sr + (kurt - 1) / 4.0 * sr * sr, 1e-12))
    dsr = norm.cdf((sr - sr0) * np.sqrt(T - 1) / denom)
    return {
        "sharpe_ann": float(sr * np.sqrt(ANN)),
        "n_trials": int(n_trials),
        "expected_max_sharpe_ann_under_null": float(sr0 * np.sqrt(ANN)),
        "deflated_sharpe_prob": float(dsr),
    }


def calibration(pit_values: np.ndarray) -> dict:
    """Is the predictive distribution the strategy bets through actually right?

    Under a correct predictive CDF the PIT values are U(0,1).  A KS test on
    them is a direct specification test; the deciles show *how* it fails
    (mass in the tails = predictive intervals too narrow).
    """
    u = np.asarray(pit_values, dtype=float)
    u = u[np.isfinite(u)]
    ks = kstest(u, "uniform")
    deciles = np.histogram(u, bins=10, range=(0, 1))[0] / len(u)
    return {
        "n": len(u),
        "mean": float(u.mean()),
        "ks_stat": float(ks.statistic),
        "ks_pvalue": float(ks.pvalue),
        "decile_freq": [float(x) for x in deciles],
        "tail_mass_5pct": float(((u < 0.05) | (u > 0.95)).mean()),
    }


def overlay(benchmark: np.ndarray, strategy: np.ndarray,
            mixes: tuple[float, ...] = (0.0, 0.25, 0.5, 1.0)) -> dict:
    """Is a weak but uncorrelated return stream worth owning next to SPY?

    A standalone Sharpe of 0.1 is not interesting on its own.  Bolted onto a
    long equity book it can still be, because portfolio Sharpe depends on
    correlation, not on the overlay's own Sharpe.  Reports the alpha regression
    (with a Newey-West correction for autocorrelated residuals) and what
    happens to the combined book at several overlay sizes.
    """
    b = np.asarray(benchmark, dtype=float)
    s = np.asarray(strategy, dtype=float)
    ok = np.isfinite(b) & np.isfinite(s)
    b, s = b[ok], s[ok]
    T = len(b)

    X = np.column_stack([np.ones(T), b])
    coef, *_ = np.linalg.lstsq(X, s, rcond=None)
    resid = s - X @ coef
    xtx_inv = np.linalg.inv(X.T @ X)
    lag = int(np.floor(4 * (T / 100) ** (2 / 9)))  # Newey-West rule of thumb
    meat = (X * resid[:, None]).T @ (X * resid[:, None])
    for l in range(1, lag + 1):
        w = 1.0 - l / (lag + 1)
        u = (X * resid[:, None])[l:]
        v = (X * resid[:, None])[:-l]
        gamma = u.T @ v
        meat += w * (gamma + gamma.T)
    cov = xtx_inv @ meat @ xtx_inv

    return {
        "correlation": float(np.corrcoef(b, s)[0, 1]),
        "alpha_ann": float(coef[0] * ANN),
        "alpha_t": float(coef[0] / np.sqrt(cov[0, 0])),
        "beta": float(coef[1]),
        "nw_lags": lag,
        "mixes": {f"{k:.2f}": performance(b + k * s) for k in mixes},
    }


def subperiods(dates, r: np.ndarray, edges: list[str]) -> dict:
    """Performance sliced by date, to see whether the edge is one era's fluke."""
    import pandas as pd

    s = pd.Series(r, index=pd.DatetimeIndex(dates)).dropna()
    out = {}
    bounds = [s.index[0]] + [pd.Timestamp(e) for e in edges] + [s.index[-1]]
    for lo, hi in zip(bounds[:-1], bounds[1:]):
        chunk = s.loc[(s.index >= lo) & (s.index < hi)]
        if len(chunk) > 60:
            out[f"{lo.date()}..{hi.date()}"] = performance(chunk.to_numpy())
    return out
