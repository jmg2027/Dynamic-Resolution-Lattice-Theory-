"""The game layer: combine experts by regret minimisation, not by fitting.

Framing.  Treat the market as an *adversary* in a repeated game.  Each day we
pick a mixture over ``N`` experts, the adversary then picks the day's return --
and it is allowed to know our algorithm.  Under that assumption you cannot ask
"which expert is right?", because the adversary would then kill exactly that
expert.  What you *can* ask for is a guarantee relative to hindsight.

Hedge (multiplicative weights) delivers one: playing weights proportional to
``exp(eta * cumulative_gain)`` gives

    (best fixed expert in hindsight) - (what we actually earned)  =  O(sqrt(T log N))

so the per-round regret vanishes as ``sqrt(log N / T)`` no matter what the
adversary does.  That is a distribution-free statement -- no stationarity, no
i.i.d., no assumption that the experts keep working.  It is the right tool for
a pool of signals that are known to decay: Hedge does not need to be told a
signal died, it defunds it automatically.

:func:`realised_regret` checks the guarantee against the actual backtest rather
than trusting the theorem's applicability.
"""

from __future__ import annotations

import numpy as np


def causal_gain_scale(pnl: np.ndarray, halflife: float = 252.0,
                      width: float = 3.0, floor: float = 1e-6) -> np.ndarray:
    """Causal EWMA of mean absolute PnL across experts, times ``width``.

    Hedge's regret bound is stated for gains in ``[0,1]``, so the PnL has to be
    squashed into that range.  Doing it with a hardcoded constant is a trap: set
    it too small and the clip saturates, at which point the exponential weights
    stop seeing *how much* an expert won and Hedge silently degenerates into a
    hit-rate contest that will happily crown a loser.  Scaling by the pool's own
    realised PnL magnitude keeps the map in its unsaturated range at every point
    in the sample, and removes the constant.
    """
    mean_abs = np.nanmean(np.abs(pnl), axis=1)
    mean_abs = np.nan_to_num(mean_abs)
    lam = 0.5 ** (1.0 / halflife)
    acc = wsum = 0.0
    out = np.empty(len(mean_abs))
    for t, v in enumerate(mean_abs):
        acc = lam * acc + (1 - lam) * v
        wsum = lam * wsum + (1 - lam)
        out[t] = acc / wsum if wsum > 0 else 0.0
    return np.maximum(out * width, floor)


def normalise_gains(pnl: np.ndarray, scale: float | np.ndarray = 0.02) -> np.ndarray:
    """Map per-day PnL into the ``[0,1]`` gain range Hedge's bound assumes.

    ``scale`` may be a constant or a causal per-day array from
    :func:`causal_gain_scale`; prefer the latter whenever the PnL magnitude of
    the expert pool is not known in advance.
    """
    s = np.asarray(scale, dtype=float)
    if s.ndim == 1:
        s = s[:, None]
    return np.clip(0.5 + pnl / (2.0 * s), 0.0, 1.0)


def hedge_weights(gains: np.ndarray, eta_scale: float = 1.0) -> np.ndarray:
    """Anytime Hedge weights.

    ``gains[t, i]`` is expert ``i``'s normalised gain *realised on day t*, which
    is known at the close of day ``t``.  The returned ``W[t]`` is therefore the
    mixture to hold from the close of ``t`` -- it depends on gains through
    ``t`` inclusive and never on the future.

    Learning rate ``eta_t = eta_scale * sqrt(8 ln N / t)`` is the horizon-free
    variant, so no backtest-length constant leaks into the weights.
    """
    T, N = gains.shape
    filled = np.nan_to_num(gains, nan=0.5)  # a missing expert scores par
    cum = np.cumsum(filled, axis=0)
    t_idx = np.arange(1, T + 1, dtype=float)[:, None]
    eta = eta_scale * np.sqrt(8.0 * np.log(max(N, 2)) / t_idx)

    score = eta * cum
    score -= score.max(axis=1, keepdims=True)  # stabilise the exponential
    w = np.exp(score)
    return w / w.sum(axis=1, keepdims=True)


def realised_regret(gains: np.ndarray, weights: np.ndarray) -> dict:
    """Compare Hedge's realised gain to the best fixed expert in hindsight."""
    T, N = gains.shape
    filled = np.nan_to_num(gains, nan=0.5)
    played = np.concatenate(([0.5], (weights[:-1] * filled[1:]).sum(axis=1)))
    per_expert = filled.sum(axis=0)
    best = per_expert.max()
    regret = best - played.sum()
    bound = np.sqrt(T * np.log(max(N, 2)) / 2.0)
    return {
        "T": T,
        "N": N,
        "hedge_gain": float(played.sum()),
        "best_expert_gain": float(best),
        "best_expert": int(per_expert.argmax()),
        "regret": float(regret),
        "bound_sqrt_T_logN_over_2": float(bound),
        "bound_respected": bool(regret <= bound),
    }
