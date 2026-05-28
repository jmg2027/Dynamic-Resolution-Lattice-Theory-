import E213.Lib.Math.Cohomology.CupAW.Core

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# Basis-pair Leibniz at (5, 1, 2) — small enumeration

For each basis indicator e_i : Cochain 5 1 (i ∈ Fin 5) and
f_j : Cochain 5 2 (j ∈ Fin 10), Leibniz holds — 5 × 10 = 50
basis pairs × 10 output indices = 500 evals (vs 327,680 for
the full ∀ α β enumeration).

Combined with `cupAW_add_left/right` (bilinearity) and
`delta_add` (linearity), this is the basis case on which the
universal lift would run.
-/

namespace E213.Lib.Math.Cohomology.CupAW.BasisLeibniz

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)

/-- Indicator basis cochain at (n, k): 1 at the i-th k-subset,
    0 elsewhere. -/
def basis (n k : Nat) (i : Fin (binom n k)) : Cochain n k :=
  fun j => i.val == j.val

/-- ★★★ Basis-pair Leibniz at (5, 1, 2) — 500-case decide. -/
theorem basis_leibniz_5_1_2 :
    ∀ i : Fin 5, ∀ k : Fin 10, ∀ j : Fin 10,
      delta (cupAW 5 1 2 (basis 5 1 i) (basis 5 2 k)) j
        = xor (cupAW 5 2 2 (delta (basis 5 1 i)) (basis 5 2 k) j)
              (cupAW 5 1 3 (basis 5 1 i) (delta (basis 5 2 k)) j) := by
  decide

/-- ★★★ Basis-pair Leibniz at (5, 2, 2) — 100 × 5 = 500-case decide.
    α : basis 5 2 i (i ∈ Fin 10), β : basis 5 2 j (j ∈ Fin 10). -/
theorem basis_leibniz_5_2_2 :
    ∀ i : Fin 10, ∀ j : Fin 10, ∀ k : Fin 5,
      delta (cupAW 5 2 2 (basis 5 2 i) (basis 5 2 j)) k
        = xor (cupAW 5 3 2 (delta (basis 5 2 i)) (basis 5 2 j) k)
              (cupAW 5 2 3 (basis 5 2 i) (delta (basis 5 2 j)) k) := by
  decide

/-- Basis-pair Leibniz at (5, 2, 1) — 10 × 5 × 10 = 500-case decide.
    α : basis 5 2 p (p ∈ Fin 10), β : basis 5 1 k (k ∈ Fin 5). -/
theorem basis_leibniz_5_2_1 :
    ∀ p : Fin 10, ∀ k : Fin 5, ∀ i : Fin (binom 5 3),
      delta (cupAW 5 2 1 (basis 5 2 p) (basis 5 1 k)) i
        = xor (cupAW 5 3 1 (delta (basis 5 2 p)) (basis 5 1 k) i)
              (cupAW 5 2 2 (basis 5 2 p) (delta (basis 5 1 k)) i) := by
  decide

/-- Basis-pair Leibniz at (5, 3, 1) — 10 × 5 × 5 = 250-case decide.
    α : basis 5 3 p (p ∈ Fin 10), β : basis 5 1 k (k ∈ Fin 5),
    output index : Fin (binom 5 4) = Fin 5.  Sister of
    `basis_leibniz_5_2_1` at the codim-3 α stratum. -/
theorem basis_leibniz_5_3_1 :
    ∀ p : Fin 10, ∀ k : Fin 5, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 p) (basis 5 1 k)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 p)) (basis 5 1 k) i)
              (cupAW 5 3 2 (basis 5 3 p) (delta (basis 5 1 k)) i) := by
  decide

end E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
