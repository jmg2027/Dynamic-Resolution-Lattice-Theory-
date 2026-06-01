import E213.Lib.Math.Cauchy.DivergenceLadder
import E213.Lib.Math.Real213.FibCassiniNat

/-!
# Depth-floor = det 1 (forward direction) — ∅-axiom

The divergence ladder (`DivergenceLadder`) measures a real's *divergence
depth* — how many finite-difference lifts its cross-determinant sequence
needs before it bottoms out at a constant (the **floor**).  Algebraic
irrationals sit at depth 0: their cross-determinant is *already* constant
(`const_reaches_floor`, docstring "φ, √2: `Wₙ = ±1`").

The P-orbit side provides the constant: for the Fibonacci convergents to
φ, `fib_cassini_norm` gives `fib(2n+2)² + 1 = fib(2n+2)·fib(2n+1) +
fib(2n+1)²` for all `n` — the Cassini cross-determinant equals 1 (det P =
1), in PURE Nat-additive form.

This file is the **hinge**: it instantiates the abstract ladder's
sequence with the *actual* convergent cross-determinant `W` and shows it
reaches the floor at depth 0 with floor value exactly 1.  So the
analysis-side floor (`const_reaches_floor`) and the atomic-side invariant
(det P = 1) are the **same** statement — the forward half of the
`depth_floor_is_det_one` brick.

Because `fib_cassini_shifted` is already Nat-additive, no `Int`
subtraction appears anywhere in the bridge.

**Open (converse)**: floor value 1 ⟹ the convergents obey the autonomous
P-step (`OrbitForcing` / `PnFibonacciUniversal`) — the "distance from
atomicity" direction.
-/

namespace E213.Lib.Math.Cauchy.DepthFloorDetOne

open E213.Lib.Math.Cauchy.DivergenceLadder (reachesFloor isConst)
open E213.Lib.Math.Real213.FibCassiniNat (fib_cassini_norm)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Tactic.NatHelper (succ_sub)

/-- The **convergent cross-determinant** sequence, as a `Nat → Nat` to
    feed the divergence ladder:
    `W n = fib(2n+2)·fib(2n+1) + fib(2n+1)² − fib(2n+2)²`. -/
def W (n : Nat) : Nat :=
  fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1)
    - fib (2 * n + 2) * fib (2 * n + 2)

/-- `W n = 1` for every `n` — the cross-determinant is the constant det P = 1.
    `fib_cassini_norm` rewrites the minuend as `subtrahend + 1`;
    `succ_sub` cancels.  No `Int` subtraction. -/
theorem W_eq_one (n : Nat) : W n = 1 := by
  show fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1)
        - fib (2 * n + 2) * fib (2 * n + 2) = 1
  rw [← fib_cassini_norm n]
  exact succ_sub _

/-- `W` is constant — it is already at the ladder floor. -/
theorem W_isConst : isConst W := fun n => by rw [W_eq_one n, W_eq_one 0]

/-- ★★ **Forward half of `depth_floor_is_det_one`.**  The convergent
    cross-determinant sequence reaches the divergence-ladder floor at depth 0
    (`⟨0, …⟩`, since `liftK 0 W = W`) and its floor value is exactly 1.

    Identifies the analysis-side floor (`const_reaches_floor`) with the
    atomic-side invariant (det P = 1): they are one statement. -/
theorem convergent_crossdet_floor_is_one :
    reachesFloor W ∧ ∀ n, W n = 1 :=
  ⟨⟨0, W_isConst⟩, W_eq_one⟩

end E213.Lib.Math.Cauchy.DepthFloorDetOne
