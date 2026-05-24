import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop53

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# CupAW Leibniz at (5, 1, 3) — per-basis decomposition

Sister to `Leibniz5_1_2_BasisDecomp` at the next β-degree.
Same meta-strategy: fix α to a basis indicator so the cupAW
expansion simplifies into per-basis scope.

For α fixed to `basis 5 1 ⟨k⟩` (k ∈ {0..4}), the per-basis
Leibniz at (5, 1, 3) decides over the full β-pattern
(1024 × 5 = 5120 evals — smaller than (5, 1, 2)'s 10 240 since
the result index space is `Fin (binom 5 4) = Fin 5`).

STRICT ∅-AXIOM.  Lifts via the same bilinearity template as
`Leibniz5_1_2` to the universal (5, 1, 3) Leibniz.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_3_BasisDecomp

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Universal.Prop53 renaming pattern → patternE

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_0. -/
theorem leibniz_basis_5_1_3_at_0 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 4),
        delta (cupAW 5 1 3 (basis 5 1 ⟨0, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 3 (delta (basis 5 1 ⟨0, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 4 (basis 5 1 ⟨0, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_1. -/
theorem leibniz_basis_5_1_3_at_1 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 4),
        delta (cupAW 5 1 3 (basis 5 1 ⟨1, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 3 (delta (basis 5 1 ⟨1, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 4 (basis 5 1 ⟨1, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_2. -/
theorem leibniz_basis_5_1_3_at_2 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 4),
        delta (cupAW 5 1 3 (basis 5 1 ⟨2, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 3 (delta (basis 5 1 ⟨2, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 4 (basis 5 1 ⟨2, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_3. -/
theorem leibniz_basis_5_1_3_at_3 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 4),
        delta (cupAW 5 1 3 (basis 5 1 ⟨3, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 3 (delta (basis 5 1 ⟨3, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 4 (basis 5 1 ⟨3, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_4. -/
theorem leibniz_basis_5_1_3_at_4 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 4),
        delta (cupAW 5 1 3 (basis 5 1 ⟨4, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 3 (delta (basis 5 1 ⟨4, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 4 (basis 5 1 ⟨4, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

/-- ★★★★★ Per-basis Leibniz capstone at (5, 1, 3). -/
theorem leibniz_basis_5_1_3_capstone :
    (∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 1 3 (basis 5 1 ⟨0, by decide⟩)
                          (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
        = xor (cupAW 5 2 3 (delta (basis 5 1 ⟨0, by decide⟩))
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
              (cupAW 5 1 4 (basis 5 1 ⟨0, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i))
    ∧ (∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 1 3 (basis 5 1 ⟨4, by decide⟩)
                          (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
        = xor (cupAW 5 2 3 (delta (basis 5 1 ⟨4, by decide⟩))
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
              (cupAW 5 1 4 (basis 5 1 ⟨4, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i)) :=
  ⟨leibniz_basis_5_1_3_at_0, leibniz_basis_5_1_3_at_4⟩

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_3_BasisDecomp
