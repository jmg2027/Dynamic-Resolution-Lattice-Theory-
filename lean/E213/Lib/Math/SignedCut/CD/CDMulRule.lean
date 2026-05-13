import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.CutSumTest

/-!
# CD Multiplication Rule (∅-axiom)

Continuation of G36 (PR #62): parametrises the **multiplication
rule** that distinguishes sign extension (ℝ), complex (ℂ),
quaternion (ℍ), ...

  * Sign:    `(a,b)·(c,d) = (a·c + b·d, a·d + b·c)`
  * Complex: `(a,b)·(c,d) = (a·c, a·d + b·c)`  (b·d flipped neg)

The pair structure carries every CD step; the rule specialises
to the field.
-/

namespace E213.Lib.Math.SignedCut.CD.CDMulRule

open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)

/-- CD multiplication rule indicator. -/
inductive CDRule where
  | signRule
  | complexRule

/-- Sign-rule multiplication. -/
def signMul (a b c d : Nat → Nat → Bool) :
    (Nat → Nat → Bool) × (Nat → Nat → Bool) :=
  (cutSum (cutMul a c) (cutMul b d), cutSum (cutMul a d) (cutMul b c))

/-- Complex-rule multiplication (positive-cut layer). -/
def complexMul (a b c d : Nat → Nat → Bool) :
    (Nat → Nat → Bool) × (Nat → Nat → Bool) :=
  (cutMul a c, cutSum (cutMul a d) (cutMul b c))

/-- ★ Rules are distinct. -/
theorem cdrule_neq : ¬ (CDRule.signRule = CDRule.complexRule) :=
  fun h => CDRule.noConfusion h

/-- ★ **Sign rule first component**: a·c + b·d. -/
theorem signMul_fst (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).1 = cutSum (cutMul a c) (cutMul b d) := rfl

/-- ★ **Sign rule second component**: a·d + b·c. -/
theorem signMul_snd (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).2 = cutSum (cutMul a d) (cutMul b c) := rfl

/-- ★ **Complex rule first component (re)**: a·c only. -/
theorem complexMul_fst (a b c d : Nat → Nat → Bool) :
    (complexMul a b c d).1 = cutMul a c := rfl

/-- ★ **Complex rule second component (im)**: a·d + b·c. -/
theorem complexMul_snd (a b c d : Nat → Nat → Bool) :
    (complexMul a b c d).2 = cutSum (cutMul a d) (cutMul b c) := rfl

/-- ★ **Cross terms agree**: signRule and complexRule give the
    same second (im / cross) component. -/
theorem mulrules_im_agree (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).2 = (complexMul a b c d).2 := rfl

end E213.Lib.Math.SignedCut.CD.CDMulRule
