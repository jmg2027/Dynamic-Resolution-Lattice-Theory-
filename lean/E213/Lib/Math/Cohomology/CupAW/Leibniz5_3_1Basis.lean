import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# Basis-pair Leibniz at (5, 3, 1) — small enumeration

α : basis 5 3 p (p ∈ Fin 10), β : basis 5 1 k (k ∈ Fin 5),
output index : Fin (binom 5 4) = Fin 5.  Total: 10 × 5 × 5 = 250
cases — small enough for direct `decide`.

Sister of `basis_leibniz_5_2_1` (codim-2 vs codim-3 α stratum).
STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1Basis

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)

/-- ★★★ Basis-pair Leibniz at (5, 3, 1) — 250-case decide.
    α : basis 5 3 p (p ∈ Fin 10), β : basis 5 1 k (k ∈ Fin 5),
    output index : Fin (binom 5 4) = Fin 5. -/
theorem basis_leibniz_5_3_1 :
    ∀ p : Fin 10, ∀ k : Fin 5, ∀ i : Fin (binom 5 4),
      delta (cupAW 5 3 1 (basis 5 3 p) (basis 5 1 k)) i
        = xor (cupAW 5 4 1 (delta (basis 5 3 p)) (basis 5 1 k) i)
              (cupAW 5 3 2 (basis 5 3 p) (delta (basis 5 1 k)) i) := by
  decide

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1Basis
