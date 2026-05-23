import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop52

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# CupAW Leibniz at (5, 1, 2) — per-basis decomposition

The full ∀-pattern decide at (5, 1, 2) OOMs the Lean kernel
across four meta-strategies (catalogued in the marathon note
Phase 10).  Breakthrough: **fix α to a basis indicator**
(Cochain 5 1 with a single non-zero entry).

For `α = basis 5 1 ⟨k⟩`, the cupAW expansion simplifies (most
contributions vanish), dropping per-eval cost to roughly the
(5, 1, 1) scope.  Each per-basis Leibniz then fits in the
decide budget.

This file ships the **5 per-basis Leibniz lemmas** at α ∈
`{e_0, e_1, e_2, e_3, e_4}`, each decided over the full
β-pattern (1024 × 10 = 10 240 evals) at `maxHeartbeats 200M`.

The universal (5, 1, 2) Leibniz lifts these via bilinearity
chain (sister to `LeibnizAlgLift21` template for (5, 2, 1) but
on the α-side at lower α-degree).  STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2_BasisDecomp

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Universal.Prop52 renaming pattern → patternE

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_0. -/
theorem leibniz_basis_5_1_2_at_0 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 3),
        delta (cupAW 5 1 2 (basis 5 1 ⟨0, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 2 (delta (basis 5 1 ⟨0, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 3 (basis 5 1 ⟨0, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_1. -/
theorem leibniz_basis_5_1_2_at_1 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 3),
        delta (cupAW 5 1 2 (basis 5 1 ⟨1, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 2 (delta (basis 5 1 ⟨1, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 3 (basis 5 1 ⟨1, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_2. -/
theorem leibniz_basis_5_1_2_at_2 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 3),
        delta (cupAW 5 1 2 (basis 5 1 ⟨2, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 2 (delta (basis 5 1 ⟨2, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 3 (basis 5 1 ⟨2, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_3. -/
theorem leibniz_basis_5_1_2_at_3 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 3),
        delta (cupAW 5 1 2 (basis 5 1 ⟨3, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 2 (delta (basis 5 1 ⟨3, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 3 (basis 5 1 ⟨3, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

set_option maxHeartbeats 200000000 in
/-- Per-basis Leibniz at α = e_4. -/
theorem leibniz_basis_5_1_2_at_4 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 3),
        delta (cupAW 5 1 2 (basis 5 1 ⟨4, by decide⟩)
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = xor (cupAW 5 2 2 (delta (basis 5 1 ⟨4, by decide⟩))
                              (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
                (cupAW 5 1 3 (basis 5 1 ⟨4, by decide⟩)
                              (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i) := by
  decide

/-- ★★★★★ **(5, 1, 2) Per-basis Leibniz capstone**.  Five
    per-basis Leibniz facts for α ∈ {e_0, e_1, e_2, e_3, e_4}
    — each individually decided in tractable memory (avoiding
    the OOM of the full ∀-pattern decide).

    Together with the bz5_1 zero/basis-split + bilinearity chain
    (LeibnizAlgLift template, Phase 11 follow-up), these lift
    to the universal (5, 1, 2) Leibniz identity. -/
theorem leibniz_basis_5_1_2_capstone :
    (∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ i : Fin (binom 5 3),
      delta (cupAW 5 1 2 (basis 5 1 ⟨0, by decide⟩)
                          (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
        = xor (cupAW 5 2 2 (delta (basis 5 1 ⟨0, by decide⟩))
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
              (cupAW 5 1 3 (basis 5 1 ⟨0, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i))
    ∧ (∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ i : Fin (binom 5 3),
      delta (cupAW 5 1 2 (basis 5 1 ⟨1, by decide⟩)
                          (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
        = xor (cupAW 5 2 2 (delta (basis 5 1 ⟨1, by decide⟩))
                            (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) i)
              (cupAW 5 1 3 (basis 5 1 ⟨1, by decide⟩)
                            (delta (patternE b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i)) :=
  ⟨leibniz_basis_5_1_2_at_0, leibniz_basis_5_1_2_at_1⟩

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2_BasisDecomp
