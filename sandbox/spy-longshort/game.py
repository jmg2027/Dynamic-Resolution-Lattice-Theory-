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


def normalise_gains(pnl: np.ndarray, scale: float = 0.02) -> np.ndarray:
    """Map per-day PnL into the ``[0,1]`` gain range Hedge's bound assumes."""
    return np.clip(0.5 + pnl / (2.0 * scale), 0.0, 1.0)


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
