import E213.Meta.Tactic.Nat213
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Universal δ²=0 Prop-lift at (3, 1)

User: hard deferred items resolution.  Extend Universal δ²=0
Prop-lift from (n, 0) to (n, 1) at concrete n.

For (3, 1): Cochain 3 1 = Fin 3 → Bool, 2³ = 8 functions.
Approach: parametrize via 3 Bool values, prove ∀ b0 b1 b2,
δ²(pattern b0 b1 b2) = 0 by decide (8-case enumeration).

Then any σ : Cochain 3 1 = pattern (σ⟨0⟩, σ⟨1⟩, σ⟨2⟩) by
funext, lift via this representation.
-/

namespace E213.Lib.Math.Cohomology.Universal.Prop31

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)

/-- Cochain 3 1 parametrized by 3 Bool values.  PURE: matches on
    `i.val : Nat` (Nat-decidable) instead of `i : Fin 3` (Fin-match
    introduces propext at def level). -/
def pattern (b0 b1 b2 : Bool) : Cochain 3 1 := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | _ => b2

/-- Any σ : Cochain 3 1 equals its pattern at every i. -/
theorem pattern_eq_at (σ : Cochain 3 1) (i : Fin 3) :
    σ i = pattern (σ ⟨0, by decide⟩)
                  (σ ⟨1, by decide⟩)
                  (σ ⟨2, by decide⟩) i := by
  obtain ⟨n, hn⟩ := i
  rcases E213.Tactic.Nat213.cases_lt_three hn with h0 | h1 | h2
  · subst h0; rfl
  · subst h1; rfl
  · subst h2; rfl

/-- δ²=0 on every pattern, all 8 Bool triples × 1 index. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 : Bool, ∀ i : Fin (binom 3 3),
      delta (delta (pattern b0 b1 b2)) i = false := by decide

/-- ★ Prop-level ∀ σ : Cochain 3 1, δ²σ = 0.  PURE via twice-applied
    `delta_pointwise_eq` (no funext at the lift step). -/
theorem dsq_zero_prop_3_1 (σ : Cochain 3 1)
    (i : Fin (binom 3 3)) : delta (delta σ) i = false := by
  let τ := pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
  have h_pat : ∀ j, σ j = τ j := pattern_eq_at σ
  have h_outer : delta (delta σ) i = delta (delta τ) i :=
    delta_pointwise_eq (delta σ) (delta τ)
      (fun j => delta_pointwise_eq σ τ h_pat j) i
  rw [h_outer]
  exact dsq_pattern _ _ _ i

/-- ★★★ Capstone: Prop-level Universal δ²=0 extends to (3, 1). -/
theorem prop_lift_capstone :
    (∀ σ : Cochain 3 0, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 0, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 3 1, ∀ i, delta (delta σ) i = false) :=
  ⟨E213.Lib.Math.Cohomology.Universal.Prop.dsq_zero_prop_3_0,
   E213.Lib.Math.Cohomology.Universal.Prop.dsq_zero_prop_5_0,
   dsq_zero_prop_3_1⟩

end E213.Lib.Math.Cohomology.Universal.Prop31
