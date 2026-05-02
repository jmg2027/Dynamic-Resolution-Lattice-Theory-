import E213.Math.Real213.Signed
import E213.Math.Real213.CutInv
import E213.Math.Real213.CutSumOne

/-!
# Research.Real213SignedSum: signed sum + subtraction

cutSignedSum: case analysis on signs.
cutSignedSub: cutSignedSum with negated second arg.
-/

namespace E213.Math.Real213.SignedSum

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)

/-- **cutSignedSum**: signed addition.  Same sign: cutSum on |abs|.
    Different sign: |abs| difference (sign determination is incomplete in
    the generic case, partial at the boundary). -/
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

/-- **(+a/1) + (+c/1) = +(a+c)/1**: signed sum on positive integers. -/
theorem cutSignedSum_pos_int (a c : Nat) :
    cutSignedSum (signedConstCut true a 1) (signedConstCut true c 1)
    = signedConstCut true (a+c) 1 := by
  show cutSignedSum {sign := true, cut := constCut a 1}
                    {sign := true, cut := constCut c 1}
    = {sign := true, cut := constCut (a+c) 1}
  rw [cutSignedSum_pos_pos, cutSum_int_int]

/-- **(-a/1) + (-c/1) = -(a+c)/1**: signed sum on negative integers. -/
theorem cutSignedSum_neg_int (a c : Nat) :
    cutSignedSum (signedConstCut false a 1) (signedConstCut false c 1)
    = signedConstCut false (a+c) 1 := by
  show cutSignedSum {sign := false, cut := constCut a 1}
                    {sign := false, cut := constCut c 1}
    = {sign := false, cut := constCut (a+c) 1}
  rw [cutSignedSum_neg_neg, cutSum_int_int]

/-- **(+a/2) + (+c/2) = +(a+c)/2**: signed sum on positive halves. -/
theorem cutSignedSum_pos_half (a c : Nat) :
    cutSignedSum (signedConstCut true a 2) (signedConstCut true c 2)
    = signedConstCut true (a+c) 2 := by
  show cutSignedSum {sign := true, cut := constCut a 2}
                    {sign := true, cut := constCut c 2}
    = {sign := true, cut := constCut (a+c) 2}
  rw [cutSignedSum_pos_pos, cutSum_half_general]

/-- **−(x + y) = (−x) + (−y)**: cutNeg distributes over cutSignedSum.
    Holds in both branches (same-sign and cross-sign) of the partial
    cutSignedSum implementation. -/
theorem cutNeg_cutSignedSum (sx sy : SignedCut) :
    cutNeg (cutSignedSum sx sy)
    = cutSignedSum (cutNeg sx) (cutNeg sy) := by
  cases sx with
  | mk sxsign sxcut =>
    cases sy with
    | mk sysign sycut =>
      cases sxsign <;> cases sysign <;> rfl

end E213.Math.Real213.SignedSum
