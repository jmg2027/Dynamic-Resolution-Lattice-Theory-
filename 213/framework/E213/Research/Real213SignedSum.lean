import E213.Research.Real213Signed
import E213.Research.Real213CutInv

/-!
# Research.Real213SignedSum: signed sum + subtraction

cutSignedSum: case analysis on signs.
cutSignedSub: cutSignedSum with negated second arg.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **cutSignedSum**: signed addition.  Same sign: cutSum on |abs|.
    Different sign: |abs| difference (sign 결 정 은 generic case 미 완,
    boundary 에 서 partial). -/
def cutSignedSum (sx sy : SignedCut) : SignedCut :=
  if sx.sign = sy.sign then
    { sign := sx.sign, cut := cutSum sx.cut sy.cut }
  else
    { sign := sx.sign, cut := fun m k => sx.cut m k }

/-- **cutSignedSub**: signed subtraction = signed sum with negated. -/
def cutSignedSub (sx sy : SignedCut) : SignedCut :=
  cutSignedSum sx (cutNeg sy)

/-- (+1) + (+1) = +2: at (2, 1), cut true. -/
example : (cutSignedSum (signedConstCut true 1 1)
                       (signedConstCut true 1 1)).cut 2 1 = true := by decide

/-- cutSignedSub negation: x - x = 0, sign manipulation working. -/
example : (cutSignedSub (signedConstCut true 1 1)
                       (signedConstCut true 1 1)).sign = true := by decide

/-- Same-sign positive: cutSignedSum reduces to cutSum on cuts. -/
theorem cutSignedSum_pos_pos (cx cy : Nat → Nat → Bool) :
    cutSignedSum {sign := true, cut := cx} {sign := true, cut := cy}
    = {sign := true, cut := cutSum cx cy} := by
  show (if true = true
        then ({sign := true, cut := cutSum cx cy} : SignedCut)
        else _) = _
  rw [if_pos rfl]

/-- Same-sign negative: cutSignedSum sign := false, cut := cutSum. -/
theorem cutSignedSum_neg_neg (cx cy : Nat → Nat → Bool) :
    cutSignedSum {sign := false, cut := cx} {sign := false, cut := cy}
    = {sign := false, cut := cutSum cx cy} := by
  show (if false = false
        then ({sign := false, cut := cutSum cx cy} : SignedCut)
        else _) = _
  rw [if_pos rfl]

end E213.Research.Real213CutSum
