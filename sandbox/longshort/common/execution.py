"""Cost-aware execution: solve for the no-trade band instead of guessing it.

The Kelly target is the optimum of a frictionless problem, so a naive book
re-optimises to it every single day and pays transaction costs 60 times a year
to chase an edge worth a couple of basis points.  The fix is not a smoothing
constant picked by eye -- it falls out of the objective once costs are in it.

Per-day utility of holding ``p`` under the fractional-Kelly problem is

    U(p) = m*p - (sigma^2 / (2*lam)) * p^2      argmax  p* = lam * m / sigma^2

and the position will be held for roughly ``h`` days before the target moves
away.  Re-optimising costs ``c * |p - p_prev|`` **now** for a benefit accruing
over ``h`` days, so the trade is worth it only if
``h * (U(p) - U(p_prev)) > c * |p - p_prev|``.  With a quadratic ``U`` and a
linear cost this has the classic closed-form solution: a **no-trade band** of
half-width

    w = lam * c / (h * sigma^2)

around the previous position, and when the band is breached you trade only to
its edge, never all the way to the frictionless target.

Both inputs are observable, not fitted: ``c`` is the commission, and ``h`` is
estimated causally from the target's own AR(1) persistence.  So this layer adds
no free parameter to the strategy.
"""

from __future__ import annotations

import numpy as np


def causal_halflife(target: np.ndarray, min_obs: int = 252,
                    floor: float = 1.0, cap: float = 60.0) -> np.ndarray:
    """Expected holding horizon ``h = 1/(1-rho)`` from the target's own AR(1).

    ``rho`` is the expanding-window lag-1 autocorrelation of the target
    position, computed from data through ``t-1`` only.
    """
    x = np.nan_to_num(target)
    lag, cur = x[:-1], x[1:]
    prod = np.concatenate(([0.0], lag * cur))
    sq = np.concatenate(([0.0], lag * lag))
    n = np.arange(len(x), dtype=float)

    cprod = np.concatenate(([0.0], np.cumsum(prod)[:-1]))
    csq = np.concatenate(([0.0], np.cumsum(sq)[:-1]))
    with np.errstate(divide="ignore", invalid="ignore"):
        rho = np.clip(cprod / csq, 0.0, 0.99)
    h = 1.0 / (1.0 - rho)
    h = np.where(n >= min_obs, h, floor)
    return np.clip(np.nan_to_num(h, nan=floor), floor, cap)


def implied_risk_aversion(alpha: np.ndarray, variance: np.ndarray,
                          floor: float = 1e-9) -> np.ndarray:
    """Back ``lambda`` out of the book instead of assuming it.

    The band half-width ``w = lambda*c/(h*sigma^2)`` is only meaningful if
    ``lambda`` is the risk aversion that actually produced the target.  For a
    single asset that is the fractional-Kelly constant, because the position
    *is* the whole risk budget.  For a portfolio it is not: each name carries a
    fraction of the risk, and reusing the single-asset constant produces a band
    tens of times wider than the positions themselves, which silently freezes
    the book.

    At a Kelly optimum ``p* = lambda * Sigma^-1 m``, so
    ``alpha = m'p* = p*'Sigma p* / lambda = variance / lambda``.  Both sides are
    observable -- the book's own forecast return and its forecast variance --
    so ``lambda = variance / alpha`` is measured rather than assumed.  It also
    stays correct when caps bind and the target is no longer an unconstrained
    optimum, which is exactly when the assumed constant goes worst wrong.
    """
    with np.errstate(divide="ignore", invalid="ignore"):
        lam = variance / alpha
    return np.where(np.isfinite(lam) & (lam > 0), lam, floor)


def no_trade_band(target: np.ndarray, sd: np.ndarray, halflife: np.ndarray,
                  cost_bps: float, lam: float | np.ndarray,
                  cap: float) -> tuple[np.ndarray, np.ndarray]:
    """Walk the band forward.  Returns ``(position, band_halfwidth)``."""
    c = cost_bps / 1e4
    with np.errstate(divide="ignore", invalid="ignore"):
        w = lam * c / (halflife * sd * sd)
    w = np.clip(np.nan_to_num(w, nan=np.inf, posinf=cap), 0.0, cap)

    n = len(target)
    pos = np.zeros(n)
    prev = 0.0
    for t in range(n):
        tgt = target[t]
        if not np.isfinite(tgt):
            pos[t] = prev
            continue
        if tgt > prev + w[t]:
            prev = min(tgt - w[t], cap)
        elif tgt < prev - w[t]:
            prev = max(tgt + w[t], -cap)
        pos[t] = prev
    return pos, w
