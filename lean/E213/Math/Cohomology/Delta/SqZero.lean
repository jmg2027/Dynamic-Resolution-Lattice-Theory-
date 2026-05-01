import E213.Math.Cohomology.Delta.Core

/-!
# Cohomology — δ² = 0 (Phase CA, file 4)

The fundamental cochain identity.  In ℤ/2 (Bool, XOR), each
(k+2)-subset's value under δ²σ counts each k-subset face twice
(once via each removal-order) — XOR of equal values is false.

This file establishes δ²=0 by `decide` at concrete cochains. A
universally-quantified version (∀ σ, ...) requires a Fintype +
DecidablePred instance for `Cochain n k` that core Lean 4 does
not provide by default; revisit in Phase CB.
-/

namespace E213.Math.Cohomology

open E213.Physics.Simplex.Counts (binom d NS NT)

/-- δ²(zero) at (3, 0). -/
theorem delta_sq_zero_zero_3_0 :
    ∀ i : Fin (binom 3 2), delta (delta (Cochain.zero 3 0)) i = false := by
  decide

/-- δ²(zero) at (5, 0). -/
theorem delta_sq_zero_zero_5_0 :
    ∀ i : Fin (binom 5 2), delta (delta (Cochain.zero 5 0)) i = false := by
  decide

/-- δ²(zero) at (5, 1). -/
theorem delta_sq_zero_zero_5_1 :
    ∀ i : Fin (binom 5 3), delta (delta (Cochain.zero 5 1)) i = false := by
  decide

/-- Vertex-0 indicator on n=5 vertices. -/
def vertex0_n5 : Cochain 5 1 := fun i => i.val = 0

/-- δ²(vertex0_n5) = zero — concrete simplicial identity at n=5. -/
theorem delta_sq_vertex0_n5 :
    ∀ i : Fin (binom 5 3), delta (delta vertex0_n5) i = false := by
  decide

/-- Vertex-2 indicator on n=5 vertices. -/
def vertex2_n5 : Cochain 5 1 := fun i => i.val = 2

theorem delta_sq_vertex2_n5 :
    ∀ i : Fin (binom 5 3), delta (delta vertex2_n5) i = false := by
  decide

/-- Edge [0,1] indicator on n=5 (colex idx 0). -/
def edge01_n5 : Cochain 5 2 := fun i => i.val = 0

theorem delta_sq_edge01_n5 :
    ∀ i : Fin (binom 5 4), delta (delta edge01_n5) i = false := by
  decide

/-- Constant-true cochain at (3, 1). -/
def all_true_3_1 : Cochain 3 1 := fun _ => true

theorem delta_sq_all_true_3_1 :
    ∀ i : Fin (binom 3 3), delta (delta all_true_3_1) i = false := by
  decide

/-- ★ Phase CA capstone: δ²=0 at every tested cochain on Δ⁴. -/
theorem phase_CA_delta_sq_zero :
    (∀ i : Fin (binom 5 3), delta (delta (Cochain.zero 5 1)) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (delta vertex0_n5) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (delta vertex2_n5) i = false)
    ∧ (∀ i : Fin (binom 5 4), delta (delta edge01_n5) i = false) := by
  decide

end E213.Math.Cohomology
