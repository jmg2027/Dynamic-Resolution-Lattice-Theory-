import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Delta.Linear
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Delta.SqZero
import E213.Lib.Math.Cohomology.Delta.V4Capstone

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Delta`.

  Coboundary δ : Cᵏ → Cᵏ⁺¹ on the 213-native cochain complex.

  ## Files

    * `Core`        — definition `δ : Cochain n k → Cochain n (k+1)`
                      via boundary-of-subset XOR sum
    * `Linear`      — δ is linear (δ commutes with XOR + scalar)
    * `Pointwise`   — pointwise rewriting rule used by SqZero
    * `SqZero`      — δ² = 0  (the cochain-complex axiom)
    * `V4Capstone`  — V₄-level Universal δ²=0 capstone
-/
