"""Causal edge estimation: how much return is one unit of signal worth *today*?

Each expert gets its own expanding-window OLS of tomorrow's excess return on
today's PIT score.  Two details matter more than the regression itself:

1. **Timing.**  The pair ``(z[s], r_fwd[s])`` only becomes observable at the
   close of ``s+1``.  So the fit used at time ``t`` sums pairs ``s <= t-1``.
   Off-by-one here is the single most common way a backtest lies.

2. **Minimax shrinkage.**  We do not bet the point estimate.  An adversary is
   allowed to pick the true slope anywhere in the confidence interval
   ``beta_hat +/- kappa * se``, and we bet against the worst member of that
   set.  Since payoff is monotone in ``|beta|`` near zero, the worst case is
   the interval endpoint closest to zero -- so the estimate is soft-thresholded
   at ``kappa`` standard errors and an expert with no statistical support
   contributes exactly nothing rather than noise.
"""

from __future__ import annotations

import numpy as np


def _causal_cumsum(v: np.ndarray) -> np.ndarray:
    """Cumulative sum shifted so index ``t`` holds the total over ``s <= t-1``."""
    c = np.cumsum(np.nan_to_num(v, nan=0.0))
    return np.concatenate(([0.0], c[:-1]))


def rolling_slope(z: np.ndarray, y: np.ndarray, min_obs: int = 504,
                  kappa: float = 1.0) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Expanding OLS slope of ``y`` on ``z`` (with intercept), causal.

    Returns ``(beta_hat, se, beta_robust)`` where ``beta_robust`` is the
    minimax soft-thresholded slope described in the module docstring.
    """
    ok = np.isfinite(z) & np.isfinite(y)
    zz = np.where(ok, z, 0.0)
    yy = np.where(ok, y, 0.0)

    n = _causal_cumsum(ok.astype(float))
    sx = _causal_cumsum(zz)
    sy = _causal_cumsum(yy)
    sxx = _causal_cumsum(zz * zz)
    sxy = _causal_cumsum(zz * yy)
    syy = _causal_cumsum(yy * yy)

    with np.errstate(divide="ignore", invalid="ignore"):
        denom = sxx - sx * sx / n
        num = sxy - sx * sy / n
        beta = num / denom
        sst = syy - sy * sy / n
        sse = np.maximum(sst - beta * num, 0.0)
        se = np.sqrt(sse / np.maximum(n - 2.0, 1.0) / denom)

    valid = (n >= min_obs) & np.isfinite(beta) & np.isfinite(se) & (denom > 0)
    beta = np.where(valid, beta, np.nan)
    se = np.where(valid, se, np.nan)

    shrunk = np.sign(beta) * np.maximum(np.abs(beta) - kappa * se, 0.0)
    return beta, se, shrunk


def ewma_vol(r: np.ndarray, halflife: float = 21.0,
             min_obs: int = 63) -> np.ndarray:
    """Causal EWMA volatility forecast: uses returns up to and including ``t``."""
    lam = 0.5 ** (1.0 / halflife)
    n = len(r)
    var = np.full(n, np.nan)
    acc = 0.0
    wsum = 0.0
    count = 0
    for t in range(n):
        v = r[t]
        if np.isfinite(v):
            acc = lam * acc + (1 - lam) * v * v
            wsum = lam * wsum + (1 - lam)
            count += 1
        if count >= min_obs and wsum > 0:
            var[t] = acc / wsum
    return np.sqrt(var)


def kelly_fraction(mean: np.ndarray, sd: np.ndarray) -> np.ndarray:
    """Continuous Kelly for a Gaussian bet: ``f* = mu / sigma^2``.

    The log-optimal fraction for a bet with mean ``mu`` and variance
    ``sigma^2`` per period.  Nothing else in the stack sets position *size* --
    Kelly is the sizing rule, which is why the strategy automatically shrinks
    into high-volatility regimes without a separate vol target.
    """
    with np.errstate(divide="ignore", invalid="ignore"):
        f = mean / (sd * sd)
    return np.where(np.isfinite(f), f, 0.0)
