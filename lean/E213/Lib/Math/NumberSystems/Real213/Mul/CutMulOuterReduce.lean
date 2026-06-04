import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulDetermined
/-!
# cutMulOuter reduce template — upstream variant

Lives in `Real213/Mul/` so upstream files (e.g., `CutPowConst.lean`)
can use it without circular dependency to FluxMVT.

The downstream FluxMVT-specific variants
(`UnitBracketReduce.cutMulOuter_unitBracket_reduce_at` and
`cutMulOuter_reduce_at`) live in
`Analysis/FluxMVT/UnitBracketReduce.lean`.  They re-export this
upstream helper for ergonomic reuse.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mul.CutMulOuterReduce

open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMulOuter)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMulDetermined (cutMulOuter_congr)

/-- ★ Generic cutMulOuter reduction (arbitrary targets).  PURE.
    Caller specifies target cuts `gL`, `gR` and an explicit `bound`. -/
theorem cutMulOuter_reduce_at
    (f g gL gR : Nat → Nat → Bool) (m k bound : Nat)
    (hL : ∀ m', m' ≤ bound → f m' k = gL m' k)
    (hR : ∀ m', m' ≤ bound → g m' k = gR m' k) :
    cutMulOuter f g k m bound bound = cutMulOuter gL gR k m bound bound :=
  cutMulOuter_congr k m bound bound f gL g gR hL hR bound (Nat.le_refl _)

end E213.Lib.Math.NumberSystems.Real213.Mul.CutMulOuterReduce
