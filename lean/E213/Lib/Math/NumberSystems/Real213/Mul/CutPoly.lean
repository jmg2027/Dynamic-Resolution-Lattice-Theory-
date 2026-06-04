import E213.Lib.Math.NumberSystems.Real213.Mul.CutPow

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
/-!
# CutPoly: polynomial evaluation at cut level

Σ_{i=0}^n a_i x^i — cut-level polynomial evaluation.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mul.CutPoly

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Mul.CutPow (cutPow)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutPow (cutScale)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)

/-- **evalPoly**: polynomial Σ_{i=0}^degree (coeffs i) * x^i. -/
def evalPoly (coeffs : Nat → Nat) (degree : Nat) (x : Nat → Nat → Bool) :
    Nat → Nat → Bool :=
  match degree with
  | 0 => constCut (coeffs 0) 1
  | n+1 => cutSum (evalPoly coeffs n x)
                  (cutScale (coeffs (n+1)) 1 (cutPow x (n+1)))

/-- 1 + x evaluated at x = 1 is 2.  Test at (m=2, k=1). -/
example : evalPoly (fun i => if i = 0 then 1 else if i = 1 then 1 else 0)
                   1 (constCut 1 1) 2 1 = true := by decide

end E213.Lib.Math.NumberSystems.Real213.Mul.CutPoly
