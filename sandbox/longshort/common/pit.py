"""Probability integral transform, applied causally in both directions.

Two distinct uses of the same theorem (``F(X) ~ U(0,1)`` when ``F`` is the true
CDF of ``X``) show up in this project:

*forward*  -- :func:`expanding_pit` maps each raw signal through its own
  expanding empirical CDF, then through ``Phi^-1``.  This is what makes a
  price-momentum score in log units and a VIX spread in vol points live on the
  same ruler, with no distributional assumption and no exploding tails.  It is
  the reason a 2008-sized outlier does not silently become a 12-sigma bet.

*inverse* -- :func:`pit_residuals` pushes the *realised* return through the
  model's own predictive CDF.  If the predictive distribution were correct the
  result would be i.i.d. uniform, so a KS test on those values is a direct
  falsification test of the forecaster.  That is the calibration check in
  :mod:`stats`.
"""

from __future__ import annotations

import numpy as np
from scipy.stats import norm


def expanding_rank(x: np.ndarray) -> np.ndarray:
    """Causal empirical CDF: ``u[t] = (#{s <= t : x[s] <= x[t]} - 0.5) / (t+1)``.

    Ties are broken by the mid-rank so that a binary signal maps to two
    stable quantile levels rather than drifting with sample size.
    NaNs propagate as NaN and are excluded from the conditioning set.
    """
    n = len(x)
    out = np.full(n, np.nan)
    seen: list[float] = []  # kept sorted
    for t in range(n):
        v = x[t]
        if not np.isfinite(v):
            continue
        lo = np.searchsorted(seen, v, side="left")
        hi = np.searchsorted(seen, v, side="right")
        seen.insert(hi, v)
        m = len(seen)
        out[t] = (lo + hi + 1) / (2.0 * m)  # mid-rank, in (0,1)
    return out


def expanding_pit(x: np.ndarray, min_obs: int = 252) -> np.ndarray:
    """Normal-score transform of ``x`` through its causal empirical CDF.

    Returns ``Phi^-1(u)``, NaN until ``min_obs`` observations have accumulated.
    """
    u = expanding_rank(x)
    finite = np.isfinite(x)
    count = np.cumsum(finite)
    u = np.where(count >= min_obs, u, np.nan)
    z = np.full_like(u, np.nan)
    ok = np.isfinite(u)
    z[ok] = norm.ppf(np.clip(u[ok], 1e-6, 1 - 1e-6))
    return z


def pit_residuals(realised: np.ndarray, mean: np.ndarray,
                  sd: np.ndarray) -> np.ndarray:
    """``F_t(r_{t+1})`` under the Gaussian predictive law ``N(mean, sd^2)``."""
    ok = np.isfinite(realised) & np.isfinite(mean) & np.isfinite(sd) & (sd > 0)
    out = np.full(len(realised), np.nan)
    out[ok] = norm.cdf((realised[ok] - mean[ok]) / sd[ok])
    return out
