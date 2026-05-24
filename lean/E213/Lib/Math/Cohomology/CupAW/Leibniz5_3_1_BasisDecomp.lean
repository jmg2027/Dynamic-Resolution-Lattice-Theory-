import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop51

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# CupAW Leibniz at (5, 3, 1) — per-basis pattern decomposition

For α fixed to `basis 5 3 ⟨k⟩` (k ∈ {0..9}), the Leibniz
identity at (5, 3, 1) is decided over the full β-pattern
(Cochain 5 1 ≃ 5 Bools via Prop51 pattern).

Per-basis decide load: 32 patterns × 5 output faces = 160
evals.  Total over 10 basis: 1600 evals.

STRICT ∅-AXIOM.  Lifts via the bilinearity template to
universal (5, 3, 1) Leibniz.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1_BasisDecomp

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Universal.Prop51 renaming pattern → patternE

/-- Per-basis Leibniz at α = basis 5 3 ⟨0⟩. -/
theorem leibniz_basis_5_3_1_at_0 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨0, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨0, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨0, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨1⟩. -/
theorem leibniz_basis_5_3_1_at_1 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨1, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨1, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨1, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨2⟩. -/
theorem leibniz_basis_5_3_1_at_2 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨2, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨2, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨2, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨3⟩. -/
theorem leibniz_basis_5_3_1_at_3 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨3, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨3, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨3, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨4⟩. -/
theorem leibniz_basis_5_3_1_at_4 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨4, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨4, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨4, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨5⟩. -/
theorem leibniz_basis_5_3_1_at_5 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨5, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨5, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨5, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨6⟩. -/
theorem leibniz_basis_5_3_1_at_6 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨6, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨6, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨6, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨7⟩. -/
theorem leibniz_basis_5_3_1_at_7 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨7, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨7, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨7, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨8⟩. -/
theorem leibniz_basis_5_3_1_at_8 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨8, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨8, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨8, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

/-- Per-basis Leibniz at α = basis 5 3 ⟨9⟩. -/
theorem leibniz_basis_5_3_1_at_9 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 ⟨9, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 ⟨9, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 3 2 (basis 5 3 ⟨9, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i) := by decide

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1_BasisDecomp
