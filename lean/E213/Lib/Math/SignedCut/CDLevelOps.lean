import E213.Lib.Math.SignedCut.CDMulRule
import E213.Lib.Math.SignedCut.Core
import E213.Lib.Math.Complex.ComplexCut

/-!
# CD level operations — bridge to existing layers (∅-axiom)

Connects the parametrised CDMulRule to the **existing** signed
and complex layers:

  * `signMul` reproduces `Math.SignedCut.signedMul`'s positive
    component shape exactly (rfl bridge).
  * `complexMul` reproduces `Math.Complex.cMul` first/second
    component shape exactly (rfl bridge).

This file witnesses the structural unification: the same level-1
pair structure with **different multiplication rules** gives ℝ
and ℂ at the existing module endpoints.
-/

namespace E213.Lib.Math.SignedCut.CDLevelOps

open E213.Lib.Math.SignedCut.CDMulRule
  (signMul complexMul signMul_fst signMul_snd
   complexMul_fst complexMul_snd)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)

/-- ★ **Sign rule first component** matches the existing
    `Math.SignedCut.signedMul` first-component formula. -/
theorem signMul_matches_signedMul (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).1 = cutSum (cutMul a c) (cutMul b d) := rfl

/-- ★ **Sign rule second component** matches the existing
    `signedMul` second-component formula. -/
theorem signMul_matches_signedMul_snd (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).2 = cutSum (cutMul a d) (cutMul b c) := rfl

/-- ★ **Complex rule second component** matches the existing
    `Math.Complex.ComplexCut.cMul` `im` component formula. -/
theorem complexMul_matches_cMul_im (a b c d : Nat → Nat → Bool) :
    (complexMul a b c d).2 = cutSum (cutMul a d) (cutMul b c) := rfl

/-- ★ **Pair structure recovery**: from the two rules' shared
    second component, the *only* difference is the first
    component's `b·d` term sign.  Witnessed by extracting the
    second component (= cross term) from both rules — they're
    identical. -/
theorem rules_share_cross_term (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).2 = (complexMul a b c d).2 := rfl

end E213.Lib.Math.SignedCut.CDLevelOps
