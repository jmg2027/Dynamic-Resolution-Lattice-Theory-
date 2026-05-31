import E213.Lib.Math.Real213.MobiusProbeTwist
import E213.Lib.Math.Real213.Core.ValidCut
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# ProbeTwistDynamics — *how* a cut wobbles under the probe-twist

`ProbeTwistFixedPoint` showed φ's cut is fixed by the probe-twist and a
transcendental's is not.  This file answers **how** the non-fixed ones move — and
the answer is exact, not merely "they drift".

The probe-twist acts on the comparison lattice by the Möbius map
`f(x) = (2x+1)/(x+1)` (the action of `P = [[2,1],[1,1]]` on the rational `m/k`).
On a **value-carrying cut** `constCut a b` (= "value `a/b`"), the twist applies the
*inverse* map to the value:

    cutThroughP (constCut (2p+q) (p+q))  =  constCut p q          (`twist_undoes_step`)

i.e. the cut of `f(p/q) = (2p+q)/(p+q)` twists back to the cut of `p/q`.  So
`cutThroughP` runs the Pell recurrence **backwards** on the value:

  - **forward** (advancing the Pell sequence, `P_numerator`/`P_denominator` step,
    `(p,q) ↦ (2p+q, p+q)`) sends the value `x ↦ f(x)`, which *contracts toward φ*
    (the convergents nest to φ, `PhiConvergence.phi_is_unique_nested_limit`); the
    distance to φ shrinks by a factor `→ 1/φ²` each step (e: `2.708 → 1.730 →
    1.634 → 1.620 → …`);
  - **the probe-twist** sends the value `x ↦ f⁻¹(x)`, which *expands away from φ*
    — it is the same map run in reverse.

φ is the **only** cut unmoved either way, because it is the common fixed point
`f(φ) = f⁻¹(φ) = φ` (its eigenratio).  Every other real has a definite forward
direction (collapse toward φ) and a definite backward direction (the probe-twist,
away from φ); the transcendental "wobble" of `ProbeTwistFixedPoint.e_not_fixed` is
precisely **one backward Pell step on the value**, `f⁻¹`.

The cut-level subtlety noted earlier (agreement of *finite-precision* cuts with
`phiCut` is not monotone under iterated probe-twisting) is now explained: probe-
twisting is the *expanding* direction, so it moves cuts *away* from `phiCut`, not
toward it — consistent with this exact identity.

All ∅-axiom.
-/

namespace E213.Lib.Math.Real213.ProbeTwistDynamics

open E213.Lib.Math.Real213.MobiusProbeTwist (cutThroughP)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Meta.Nat.PureNat (add_mul mul_assoc)

/-! ## §1 — the additive expansion atoms (PURE) -/

private theorem fc (w x y z : Nat) : w + x + (y + z) = (w + z) + (x + y) := by
  calc w + x + (y + z) = w + (x + (y + z)) := Nat.add_assoc w x (y+z)
    _ = w + (x + y + z) := by rw [Nat.add_assoc x y z]
    _ = w + (z + (x + y)) := by rw [Nat.add_comm (x+y) z]
    _ = (w + z) + (x + y) := (Nat.add_assoc w z (x+y)).symm

private theorem eL (p q m k : Nat) :
    (2*p+q)*(m+k) = (2*(p*m) + q*k) + (2*(p*k) + q*m) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, mul_assoc 2 p m, mul_assoc 2 p k]
  exact fc (2*(p*m)) (2*(p*k)) (q*m) (q*k)

private theorem eR (p q m k : Nat) :
    (p+q)*(2*m+k) = (2*(p*m) + q*k) + (p*k + 2*(q*m)) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add,
      show p*(2*m) = 2*(p*m) from by rw [Nat.mul_comm p (2*m), mul_assoc 2 m p, Nat.mul_comm m p],
      show q*(2*m) = 2*(q*m) from by rw [Nat.mul_comm q (2*m), mul_assoc 2 m q, Nat.mul_comm m q]]
  exact fc (2*(p*m)) (p*k) (2*(q*m)) (q*k)

private theorem te1 (x y : Nat) : 2*x + y = (x+y) + x := by
  rw [Nat.two_mul, Nat.add_assoc, Nat.add_comm x y, ← Nat.add_assoc, Nat.add_comm y x]
private theorem te2 (x y : Nat) : x + 2*y = (x+y) + y := by rw [Nat.two_mul, ← Nat.add_assoc]

/-! ## §2 — the Möbius value-equivalence -/

/-- The order test through the twist matches the back-stepped test: `(2p+q)/(p+q)
    ≤ m/k ⟺ p/q ≤ m/k`.  `f(p/q) ≤ m/k ⟺ p/q ≤ f⁻¹(m/k)` — all additive, no
    subtraction. -/
theorem prop_equiv_pq (p q m k : Nat) :
    ((2*p+q)*(m+k) ≤ (p+q)*(2*m+k)) ↔ (p*k ≤ q*m) := by
  rw [eL, eR]
  constructor
  · intro h
    have h1 : 2*(p*k)+q*m ≤ p*k+2*(q*m) := E213.Tactic.NatHelper.le_of_add_le_add_left h
    rw [te1 (p*k) (q*m), te2 (p*k) (q*m)] at h1
    exact E213.Tactic.NatHelper.le_of_add_le_add_left h1
  · intro h
    apply Nat.add_le_add_left
    rw [te1 (p*k) (q*m), te2 (p*k) (q*m)]
    exact Nat.add_le_add_left h (p*k+q*m)

/-! ## §3 — the twist runs one Pell step backwards on the value -/

/-- ★★★ **The probe-twist undoes one Pell forward-step on the value.**  A cut of
    value `f(p/q) = (2p+q)/(p+q)`, viewed through the probe-twist, *is* the cut of
    value `p/q`:

        cutThroughP (constCut (2p+q) (p+q)) m k = constCut p q m k    (∀ m k).

    So `cutThroughP` = `f⁻¹` on values = the Pell recurrence run in reverse.  Since
    advancing the Pell sequence (`f`) contracts every value toward φ, the twist
    (`f⁻¹`) expands away from it — and only φ, the common fixed point `f(φ) =
    f⁻¹(φ) = φ`, stays put.  This *is* how a non-φ cut wobbles: one backward step. -/
theorem twist_undoes_step (p q m k : Nat) :
    cutThroughP (constCut (2*p+q) (p+q)) m k = constCut p q m k := by
  show decide ((2*p+q)*(m+k) ≤ (p+q)*(2*m+k)) = decide (p*k ≤ q*m)
  by_cases h : p*k ≤ q*m
  · rw [decide_eq_true ((prop_equiv_pq p q m k).mpr h), decide_eq_true h]
  · rw [decide_eq_false (fun hc => h ((prop_equiv_pq p q m k).mp hc)),
        decide_eq_false h]

end E213.Lib.Math.Real213.ProbeTwistDynamics
