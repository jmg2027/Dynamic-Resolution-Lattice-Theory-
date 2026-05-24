import E213.Lib.Math.Real213.Mobius213SternBrocot
import E213.Lib.Math.Real213.NValidCut
import E213.Lib.Math.Real213.Sum.CutSumN
import E213.Lib.Math.Real213.Sum.CutSumTest

/-!
# Mobius213SternBrocotApps — Stern-Brocot view of the cut framework

Practical consequences of `cutEq_iff_sternBrocotEq_and_zero`
(`Mobius213SternBrocot.lean`) applied to the existing 213 cut
infrastructure: `ValidCutN N`'s `is_at_denom` factors through
Stern-Brocot equivalence, and `cutSumN N` is Stern-Brocot
congruent in both arguments (modulo the (0, 0) side condition).

For canonical 213 cuts — `constCut a N` and everything built
from it — the value at (0, 0) is `decide (a * 0 ≤ N * 0) =
decide (0 ≤ 0) = true`, so the side condition is automatic.
On these cuts, Stern-Brocot equivalence and pointwise cut
equality coincide simpliciter: the mediant-closure Stern-Brocot
equivalence IS the cut framework's notion of equality.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Real213.Mobius213SternBrocotApps

open E213.Lib.Math.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.Real213.Mobius213SternBrocot
  (sternBrocotEq cutEq_of_sternBrocotEq cutEq_iff_sternBrocotEq_and_zero
   sternBrocotEq_of_cutEq)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Sum.CutSumN
  (cutSumN cutSumN_cutEq_left cutSumN_cutEq_right)
open E213.Lib.Math.Real213.NValidCut (ValidCutN ofValidCutN addN)

/-! ## §1 — The canonical (0, 0) constant -/

/-- The constant cut `constCut a N` evaluates to `true` at
    `(0, 0)`: the inequality `a * 0 ≤ N * 0` holds trivially.
    The cut framework's universal (0, 0)-true convention. -/
theorem constCut_zero_zero (a N : Nat) : constCut a N 0 0 = true := by
  show decide (a * 0 ≤ N * 0) = true
  apply decide_eq_true
  exact Nat.le_refl _

/-- A `ValidCutN N` always has `cut 0 0 = true`, transported via
    `is_at_denom` from the canonical `constCut_zero_zero`. -/
theorem validCutN_zero_zero {N : Nat} (v : ValidCutN N) :
    v.cut 0 0 = true := by
  have h := v.is_at_denom 0 0
  rw [h]
  exact constCut_zero_zero v.represents N

/-! ## §2 — `is_at_denom` factors through `sternBrocotEq` -/

/-- ★★★ **`is_at_denom` (= `cutEq cut (constCut a N)`) iff
    Stern-Brocot equivalence to the canonical denominator-N cut
    plus the canonical (0, 0)-true property.**  Direct corollary
    of `cutEq_iff_sternBrocotEq_and_zero` + `constCut_zero_zero`.

    Concrete realisation of the conjecture that every 213
    equality definition factors through `sternBrocotEq`: here,
    the `cutEq` inside `ValidCutN.is_at_denom`. -/
theorem is_at_denom_iff_sternBrocotEq
    (cut : Nat → Nat → Bool) (a N : Nat) :
    cutEq cut (constCut a N)
      ↔ sternBrocotEq cut (constCut a N) ∧ cut 0 0 = true := by
  constructor
  · intro h
    refine ⟨sternBrocotEq_of_cutEq cut (constCut a N) h, ?_⟩
    rw [h 0 0]
    exact constCut_zero_zero a N
  · intro ⟨hSB, h00⟩
    apply cutEq_of_sternBrocotEq cut (constCut a N) hSB
    rw [h00, constCut_zero_zero a N]

/-! ## §3 — Stern-Brocot congruence for `cutSumN N` -/

/-- ★★ Stern-Brocot congruence of `cutSumN N` in the left
    argument: SB-equal left arguments give pointwise equal sums
    (under a (0, 0) side condition).  Routed via
    `cutEq_of_sternBrocotEq` + `cutSumN_cutEq_left`. -/
theorem cutSumN_sternBrocotEq_left
    (N : Nat) (cx cx' cy : Nat → Nat → Bool)
    (h : sternBrocotEq cx cx') (h00 : cx 0 0 = cx' 0 0) (m k : Nat) :
    cutSumN N cx cy m k = cutSumN N cx' cy m k :=
  cutSumN_cutEq_left N cx cx' cy
    (cutEq_of_sternBrocotEq cx cx' h h00) m k

/-- ★★ Stern-Brocot congruence of `cutSumN N` in the right
    argument; analogous to `cutSumN_sternBrocotEq_left`. -/
theorem cutSumN_sternBrocotEq_right
    (N : Nat) (cx cy cy' : Nat → Nat → Bool)
    (h : sternBrocotEq cy cy') (h00 : cy 0 0 = cy' 0 0) (m k : Nat) :
    cutSumN N cx cy m k = cutSumN N cx cy' m k :=
  cutSumN_cutEq_right N cx cy cy'
    (cutEq_of_sternBrocotEq cy cy' h h00) m k

/-! ## §4 — `ValidCutN N` is closed under Stern-Brocot view

For `ValidCutN N` instances the (0, 0)-true side condition is
automatic (`validCutN_zero_zero`), so Stern-Brocot equivalence
between the `cut` fields is equivalent to pointwise cut equality.
This makes `sternBrocotEq` the canonical "same denominator-N
ratio" relation on `ValidCutN N`. -/

/-- ★★★ For `ValidCutN N` instances, Stern-Brocot equivalence of
    the underlying cut functions implies pointwise equality —
    the (0, 0) side condition is automatic. -/
theorem validCutN_cutEq_of_sternBrocotEq
    {N : Nat} (vx vy : ValidCutN N)
    (h : sternBrocotEq vx.cut vy.cut) :
    cutEq vx.cut vy.cut := by
  apply cutEq_of_sternBrocotEq vx.cut vy.cut h
  rw [validCutN_zero_zero vx, validCutN_zero_zero vy]

/-- ★★ The converse: pointwise equality implies Stern-Brocot
    equivalence on `ValidCutN N` cuts. -/
theorem validCutN_sternBrocotEq_of_cutEq
    {N : Nat} (vx vy : ValidCutN N)
    (h : cutEq vx.cut vy.cut) :
    sternBrocotEq vx.cut vy.cut :=
  sternBrocotEq_of_cutEq vx.cut vy.cut h

/-- ★★★★★ **Full bidirectional bridge on `ValidCutN N`**:
    `cutEq ↔ sternBrocotEq` on cut fields (the (0, 0) condition
    drops out automatically).  The canonical-equivalence
    conjecture realised on the bundled `ValidCutN N` framework:
    every equality of `ValidCutN N`-cuts IS Stern-Brocot
    equivalence. -/
theorem validCutN_cutEq_iff_sternBrocotEq
    {N : Nat} (vx vy : ValidCutN N) :
    cutEq vx.cut vy.cut ↔ sternBrocotEq vx.cut vy.cut :=
  ⟨validCutN_sternBrocotEq_of_cutEq vx vy,
   validCutN_cutEq_of_sternBrocotEq vx vy⟩

end E213.Lib.Math.Real213.Mobius213SternBrocotApps
