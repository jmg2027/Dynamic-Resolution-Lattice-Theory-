import E213.Math.Cohomology.Cochain.Core
import E213.Math.Cohomology.Cochain.V5Decomp
import E213.Math.Cohomology.Cochain.V5_1DecompR
import E213.Math.Cohomology.Cochain.V5_2Decomp

/-! Spec-as-code entry point for `E213.Math.Cohomology.Cochain`.

  213-native cochain complex foundation.

  ## Files

    * `Core`         — `Cochain n k = Fin (binom n k) → Bool`
                       type + zero + add (XOR / mod-2 sum)
    * `V5Decomp`     — V₅ cochain decomposition (per-i pattern lift)
    * `V5_1DecompR`  — (5, 1) decomposition R-variant
    * `V5_2Decomp`   — (5, 2) decomposition

  These decomposition lemmas underpin the cup-AW machinery
  (`CupAW/`) by exposing every Cochain as a finite XOR sum
  of patterns that `decide` can close.
-/
