import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop54

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# CupAW Leibniz at (5, 1, 4) — per-basis decomposition

Extends the per-basis Leibniz sequence from (5, 1, 2), (5, 1, 3)
to the next β-degree.  Per-basis decide load: 32 × 1 = 32 evals
(`binom 5 5 = 1`) — the smallest in the (5, 1, b) family.

For α fixed to `basis 5 1 ⟨k⟩` (k ∈ {0..4}), the Leibniz
identity at (5, 1, 4) is decided over the full β-pattern.

STRICT ∅-AXIOM.  Lifts via the bilinearity template to
universal (5, 1, 4) Leibniz.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_4_BasisDecomp

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Universal.Prop54 renaming pattern → patternE

/-- Per-basis Leibniz at α = e_0. -/
theorem leibniz_basis_5_1_4_at_0 :
    ∀ b0 b1 b2 b3 b4 : Bool,
      ∀ i : Fin (binom 5 5),
        delta (cupAW 5 1 4 (basis 5 1 ⟨0, by decide⟩)
                            (patternE b0 b1 b2 b3 b4)) i
          = xor (cupAW 5 2 4 (delta (basis 5 1 ⟨0, by decide⟩))
                              (patternE b0 b1 b2 b3 b4) i)
                (cupAW 5 1 5 (basis 5 1 ⟨0, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4)) i) := by
  decide

/-- Per-basis Leibniz at α = e_1. -/
theorem leibniz_basis_5_1_4_at_1 :
    ∀ b0 b1 b2 b3 b4 : Bool,
      ∀ i : Fin (binom 5 5),
        delta (cupAW 5 1 4 (basis 5 1 ⟨1, by decide⟩)
                            (patternE b0 b1 b2 b3 b4)) i
          = xor (cupAW 5 2 4 (delta (basis 5 1 ⟨1, by decide⟩))
                              (patternE b0 b1 b2 b3 b4) i)
                (cupAW 5 1 5 (basis 5 1 ⟨1, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4)) i) := by
  decide

/-- Per-basis Leibniz at α = e_2. -/
theorem leibniz_basis_5_1_4_at_2 :
    ∀ b0 b1 b2 b3 b4 : Bool,
      ∀ i : Fin (binom 5 5),
        delta (cupAW 5 1 4 (basis 5 1 ⟨2, by decide⟩)
                            (patternE b0 b1 b2 b3 b4)) i
          = xor (cupAW 5 2 4 (delta (basis 5 1 ⟨2, by decide⟩))
                              (patternE b0 b1 b2 b3 b4) i)
                (cupAW 5 1 5 (basis 5 1 ⟨2, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4)) i) := by
  decide

/-- Per-basis Leibniz at α = e_3. -/
theorem leibniz_basis_5_1_4_at_3 :
    ∀ b0 b1 b2 b3 b4 : Bool,
      ∀ i : Fin (binom 5 5),
        delta (cupAW 5 1 4 (basis 5 1 ⟨3, by decide⟩)
                            (patternE b0 b1 b2 b3 b4)) i
          = xor (cupAW 5 2 4 (delta (basis 5 1 ⟨3, by decide⟩))
                              (patternE b0 b1 b2 b3 b4) i)
                (cupAW 5 1 5 (basis 5 1 ⟨3, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4)) i) := by
  decide

/-- Per-basis Leibniz at α = e_4. -/
theorem leibniz_basis_5_1_4_at_4 :
    ∀ b0 b1 b2 b3 b4 : Bool,
      ∀ i : Fin (binom 5 5),
        delta (cupAW 5 1 4 (basis 5 1 ⟨4, by decide⟩)
                            (patternE b0 b1 b2 b3 b4)) i
          = xor (cupAW 5 2 4 (delta (basis 5 1 ⟨4, by decide⟩))
                              (patternE b0 b1 b2 b3 b4) i)
                (cupAW 5 1 5 (basis 5 1 ⟨4, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4)) i) := by
  decide

/-- ★★★★★ Per-basis Leibniz capstone at (5, 1, 4). -/
theorem leibniz_basis_5_1_4_capstone :
    (∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 5),
      delta (cupAW 5 1 4 (basis 5 1 ⟨0, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 2 4 (delta (basis 5 1 ⟨0, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 1 5 (basis 5 1 ⟨0, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i))
    ∧ (∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 5),
      delta (cupAW 5 1 4 (basis 5 1 ⟨4, by decide⟩)
                          (patternE b0 b1 b2 b3 b4)) i
        = xor (cupAW 5 2 4 (delta (basis 5 1 ⟨4, by decide⟩))
                            (patternE b0 b1 b2 b3 b4) i)
              (cupAW 5 1 5 (basis 5 1 ⟨4, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4)) i)) :=
  ⟨leibniz_basis_5_1_4_at_0, leibniz_basis_5_1_4_at_4⟩

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_4_BasisDecomp
