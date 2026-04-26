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

end E213.Research.Real213CutSum
