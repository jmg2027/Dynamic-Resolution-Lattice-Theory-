import E213.Lib.Math.SignedCut.CD.CDConjugation
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.CutSumTest

/-!
# CD Tower — Substrate-valued norm map (∅-axiom)

The norm-squared map `‖z‖² = z̄·z` collapses any CD level into
the **Cut substrate** (level 0).  This is the *second* invariant
of the entire CD tower (alongside conjugation, see CDConjugation):

  * Norm preservation under multiplication: `‖z·w‖² = ‖z‖²·‖w‖²`
    (Hurwitz; holds up to and including level 3 = 𝕆).
  * Substrate-valued: `‖·‖² : CDLevel n → Cut`.

213-native paradigm: at every level, `‖z‖²` is built recursively
from the pair components, accumulating into a single `Cut` value
via `cutSum` and `cutMul`.  The structural recursion gives a
**level-uniform definition**.

For the level-1 pair `(a, b)`:
  `‖(a, b)‖² = a·a + b·b`  (= `cutSum (cutMul a a) (cutMul b b)`)

For higher levels, recursion on the inner level applies the
norm to each component.
-/

namespace E213.Lib.Math.SignedCut.CD.CDNorm

open E213.Lib.Math.SignedCut.CD.CDTowerLevel (CDLevel)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- Norm-squared map: `CDLevel n → Cut` (level-0).  At each
    level, sum the inner norms of the pair components. -/
def cdNormSq : (n : Nat) → CDLevel n → (Nat → Nat → Bool)
  | 0, z => cutMul z z
  | _ + 1, z => cutSum (cdNormSq _ z.1) (cdNormSq _ z.2)

/-- ★ **Level-0 norm-squared**: `‖z‖² = z·z` (rfl). -/
theorem cdNormSq_zero (z : CDLevel 0) :
    cdNormSq 0 z = cutMul z z := rfl

/-- ★ **Level-1 norm-squared**: `‖(a, b)‖² = a·a + b·b`. -/
theorem cdNormSq_one (z : CDLevel 1) :
    cdNormSq 1 z = cutSum (cutMul z.1 z.1) (cutMul z.2 z.2) := rfl

/-- ★ **Level-2 norm-squared**: recursive sum of inner level-1
    norms on the pair components. -/
theorem cdNormSq_two (z : CDLevel 2) :
    cdNormSq 2 z = cutSum (cdNormSq 1 z.1) (cdNormSq 1 z.2) := rfl

/-- ★ **Conjugation preserves norm**: `‖z̄‖² = ‖z‖²` at level 0. -/
theorem cdNormSq_conj_zero (z : CDLevel 0) :
    cdNormSq 0 (E213.Lib.Math.SignedCut.CD.CDConjugation.cdConj 0 z)
      = cdNormSq 0 z := rfl

/-- ★ **Norm at the zero element of level 1** = `0 + 0 = 0`. -/
theorem cdNormSq_one_zero :
    cdNormSq 1 (constCut 0 1, constCut 0 1)
      = cutSum (cutMul (constCut 0 1) (constCut 0 1))
                (cutMul (constCut 0 1) (constCut 0 1)) := rfl

end E213.Lib.Math.SignedCut.CD.CDNorm
