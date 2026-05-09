import E213.Lib.Math.Cohomology.Fractal.Level
import E213.Lib.Math.UniverseChain.Recursion
import E213.Lib.Math.GenerationRule.TriangleIteration
import E213.Lib.Math.UniverseChain.BipartiteFractal

/-!
# Steps 5,6 — Finite fractal vs infinite triangle iteration (∅-axiom)

Vertex-replication map K₅ → K_{25}: `Fin 5 × Fin 5 → Fin 25`.

**Proven**: low-iter `triIter 2 k` fits inside `numV (k+1)` for k ≤ 4.
**Refuted**: strict "finite K_{25} contains infinite recursion" —
`triIter 2 5 = 26796 > 25 = numV 2`.
-/

namespace E213.Lib.Math.UniverseChain.FiniteContainsInfinite

open E213.Lib.Math.Cohomology.Fractal.Level (numV)
open E213.Lib.Math.GenerationRule.TriangleIteration (triIter T)

/-- Replicate: K₅ × K₅ → K_{25} via `5*i + j`. -/
def replicate (i j : Fin 5) : Fin 25 :=
  ⟨5 * i.val + j.val, by
    have h1 : i.val ≤ 4 := Nat.le_of_lt_succ i.isLt
    have h2 : j.val ≤ 4 := Nat.le_of_lt_succ j.isLt
    have h3 : 5 * i.val ≤ 5 * 4 := Nat.mul_le_mul_left 5 h1
    have h4 : 5 * i.val + j.val ≤ 20 + 4 :=
      Nat.add_le_add h3 h2
    exact Nat.lt_of_le_of_lt h4 (by decide)⟩

/-- ★ Replicate is injective. -/
theorem replicate_injective (i j i' j' : Fin 5)
    (h : replicate i j = replicate i' j') : i = i' ∧ j = j' := by
  have hv : 5 * i.val + j.val = 5 * i'.val + j'.val :=
    Fin.mk.inj h
  have hj_lt : j.val < 5 := j.isLt
  have hj'_lt : j'.val < 5 := j'.isLt
  have h_i : i.val = i'.val := by omega
  have h_j : j.val = j'.val := by omega
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

/-- ★ For any k ≤ 4, some L works: triIter 2 k ≤ numV L. -/
theorem any_iter_fits_some_level (k : Nat) (hk : k ≤ 4) :
    ∃ L, triIter 2 k ≤ numV L := by
  refine ⟨k + 1, ?_⟩
  match k, hk with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide

/-- ★★★ **Steps 5,6 capstone**. -/
theorem step5_6_bundle :
    numV 2 = numV 1 * numV 1
    ∧ triIter 2 4 ≤ numV 4
    ∧ ¬ (triIter 2 5 ≤ numV 2) :=
  ⟨replicate_image_card, finite_bounds_finite_iter.2.2.2.2,
   k25_does_not_contain_iter5⟩

end E213.Lib.Math.UniverseChain.FiniteContainsInfinite
