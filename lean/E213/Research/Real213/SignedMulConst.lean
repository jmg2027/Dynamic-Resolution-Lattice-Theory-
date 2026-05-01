import E213.Research.Real213.Signed
import E213.Research.Real213.CutMulOne
import E213.Research.Real213.CutSumZero

/-!
# Research.Real213SignedMulConst: signed multiplication closed forms

cutSignedMul on positive/negative const cuts at the simplest cases,
composing cutMul_one_one, cutMul_zero_zero, cutMul_one_const into
signed identities.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- (+1)(+1) = +1 as signed cut. -/
theorem cutSignedMul_one_one_pos :
    cutSignedMul (signedConstCut true 1 1) (signedConstCut true 1 1)
    = signedConstCut true 1 1 := by
  show ({ sign := true == true,
          cut := cutMul (constCut 1 1) (constCut 1 1) } : SignedCut)
       = signedConstCut true 1 1
  rw [cutMul_one_one]
  rfl

/-- (−1)(−1) = +1 as signed cut. -/
theorem cutSignedMul_one_one_neg :
    cutSignedMul (signedConstCut false 1 1) (signedConstCut false 1 1)
    = signedConstCut true 1 1 := by
  show ({ sign := false == false,
          cut := cutMul (constCut 1 1) (constCut 1 1) } : SignedCut)
       = signedConstCut true 1 1
  rw [cutMul_one_one]
  rfl

/-- (+1)(−1) = −1 as signed cut. -/
theorem cutSignedMul_pos_neg :
    cutSignedMul (signedConstCut true 1 1) (signedConstCut false 1 1)
    = signedConstCut false 1 1 := by
  show ({ sign := true == false,
          cut := cutMul (constCut 1 1) (constCut 1 1) } : SignedCut)
       = signedConstCut false 1 1
  rw [cutMul_one_one]
  rfl

/-- (+0)(+0) = +0 as signed cut. -/
theorem cutSignedMul_zero_zero :
    cutSignedMul (signedConstCut true 0 1) (signedConstCut true 0 1)
    = signedConstCut true 0 1 := by
  show ({ sign := true == true,
          cut := cutMul (constCut 0 1) (constCut 0 1) } : SignedCut)
       = signedConstCut true 0 1
  rw [cutMul_zero_zero]
  rfl

/-- (+1)(+a/b) = +(a/b): signed multiplicative identity (positive). -/
theorem cutSignedMul_one_const_pos (a b : Nat) :
    cutSignedMul (signedConstCut true 1 1) (signedConstCut true a b)
    = signedConstCut true a b := by
  show ({ sign := true == true,
          cut := cutMul (constCut 1 1) (constCut a b) } : SignedCut)
       = signedConstCut true a b
  rw [cutMul_one_const]
  rfl

end E213.Research.Real213.CutSum
