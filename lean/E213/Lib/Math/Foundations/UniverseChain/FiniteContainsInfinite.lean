import E213.Lib.Math.Cohomology.Fractal.Level
import E213.Lib.Math.Foundations.UniverseChain.Recursion
import E213.Lib.Math.Geometry.GenerationRule.TriangleIteration
import E213.Lib.Math.Foundations.UniverseChain.BipartiteFractal
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper

/-!
# Steps 5,6 — Finite fractal vs infinite triangle iteration (∅-axiom)

Vertex-replication map K₅ → K_{25}: `Fin 5 × Fin 5 → Fin 25`.

**Proven**: low-iter `triIter 2 k` fits inside `numV (k+1)` for k ≤ 4.
**Refuted**: strict "finite K_{25} contains infinite recursion" —
`triIter 2 5 = 26796 > 25 = numV 2`.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.FiniteContainsInfinite

open E213.Lib.Math.Cohomology.Fractal.Level (numV)
open E213.Lib.Math.Geometry.GenerationRule.TriangleIteration (triIter T)

/-- Replicate: K₅ × K₅ → K_{25} via `5*i + j`. -/
def replicate (i j : Fin 5) : Fin 25 :=
  ⟨5 * i.val + j.val, by
    have h1 : i.val ≤ 4 := Nat.le_of_lt_succ i.isLt
    have h2 : j.val ≤ 4 := Nat.le_of_lt_succ j.isLt
    have h3 : 5 * i.val ≤ 5 * 4 := Nat.mul_le_mul_left 5 h1
    have h4 : 5 * i.val + j.val ≤ 20 + 4 :=
      Nat.add_le_add h3 h2
    exact Nat.lt_of_le_of_lt h4 (by decide)⟩

/-- ★ Replicate is injective.  PURE — explicit mod-5 + cancellation. -/
theorem replicate_injective (i j i' j' : Fin 5)
    (h : replicate i j = replicate i' j') : i = i' ∧ j = j' := by
  have hv : 5 * i.val + j.val = 5 * i'.val + j'.val :=
    Fin.mk.inj h
  -- Step 1: j.val = j'.val via (5*i+j) % 5 = j (since j < 5).
  have h_mod_lhs : (5 * i.val + j.val) % 5 = j.val := by
    rw [E213.Meta.Nat.AddMod213.add_mod_left (by decide : 0 < 5)]
    rw [E213.Tactic.NatHelper.mul_mod_right]
    show (0 + j.val) % 5 = j.val
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt j.isLt
  have h_mod_rhs : (5 * i'.val + j'.val) % 5 = j'.val := by
    rw [E213.Meta.Nat.AddMod213.add_mod_left (by decide : 0 < 5)]
    rw [E213.Tactic.NatHelper.mul_mod_right]
    show (0 + j'.val) % 5 = j'.val
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt j'.isLt
  have h_j : j.val = j'.val := by
    have h_mod_eq : (5 * i.val + j.val) % 5 = (5 * i'.val + j'.val) % 5 :=
      congrArg (· % 5) hv
    rw [h_mod_lhs, h_mod_rhs] at h_mod_eq
    exact h_mod_eq
  -- Step 2: i.val = i'.val via Nat213.add_right_cancel + mul_left_cancel_pos.
  have h_sub : 5 * i.val + j'.val = 5 * i'.val + j'.val := by
    have := hv
    rw [h_j] at this; exact this
  have h_5i : 5 * i.val = 5 * i'.val :=
    E213.Tactic.NatHelper.add_right_cancel h_sub
  have h_i : i.val = i'.val :=
    E213.Tactic.NatHelper.mul_left_cancel_pos (by decide : (0:Nat) < 5) h_5i
  exact ⟨Fin.ext h_i, Fin.ext h_j⟩

/-- ★ Replicate image cardinality: `numV 2 = numV 1 * numV 1`. -/
theorem replicate_image_card : numV 2 = numV 1 * numV 1 := by decide

/-- ★ Low-iter fit: `triIter 2 k ≤ numV (k+1)` for k ≤ 4. -/
theorem finite_bounds_finite_iter :
    triIter 2 0 ≤ numV 1
    ∧ triIter 2 1 ≤ numV 1
    ∧ triIter 2 2 ≤ numV 2
    ∧ triIter 2 3 ≤ numV 3
    ∧ triIter 2 4 ≤ numV 4 := by decide

/-- ★ **Refutation**: K_{25} does NOT contain triIter 2 5. -/
theorem k25_does_not_contain_iter5 :
    ¬ (triIter 2 5 ≤ numV 2) := by decide

/-- ★ For any k ≤ 4, some L works: triIter 2 k ≤ numV L.
    PURE — explicit case split via `cases_lt_five` on `k < 5` (= k ≤ 4). -/
theorem any_iter_fits_some_level (k : Nat) (hk : k ≤ 4) :
    ∃ L, triIter 2 k ≤ numV L := by
  refine ⟨k + 1, ?_⟩
  have hk_lt : k < 5 := Nat.lt_succ_of_le hk
  rcases E213.Tactic.NatHelper.cases_lt_five hk_lt
    with hk0 | hk1 | hk2 | hk3 | hk4
  · subst hk0; decide
  · subst hk1; decide
  · subst hk2; decide
  · subst hk3; decide
  · subst hk4; decide

/-- ★★★ **Steps 5,6 capstone**. -/
theorem step5_6_bundle :
    numV 2 = numV 1 * numV 1
    ∧ triIter 2 4 ≤ numV 4
    ∧ ¬ (triIter 2 5 ≤ numV 2) :=
  ⟨replicate_image_card, finite_bounds_finite_iter.2.2.2.2,
   k25_does_not_contain_iter5⟩

end E213.Lib.Math.Foundations.UniverseChain.FiniteContainsInfinite
