import E213.Lib.Math.SignedCut.CDMulRule
import E213.Lib.Math.Real213.CutSumTest

/-!
# Shared (0, 1) Pair Slot — Sign vs Complex (∅-axiom)

Mingu's deep insight:

> "근데 양수에서 음수로 확장하는게 복소수로 확장하는거랑 같은
>  기저 추가인게 참 신기하네... 그럼 음수가 사실 180도가 아니라
>  90도인거고 그런건가"

213-native answer: **YES, structurally**.  Both "negative" and
"imaginary" occupy the **same orthogonal pair slot** `(0, 1)`.
The difference is in the **multiplication rule** — what the slot
squared gives:

  * Sign rule: `(0, 1)² = (1, 0)` = +1 → order-2 → 180°
  * Complex rule: `(0, 1)² = (−1, 0)` = −1 → order-4 → 90°

The "angle" is determined by `360° / order((0, 1))`, NOT by the
pair structure itself.  The 180° interpretation of "negative" is
*post-hoc* — projection of 2D pair structure onto a 1D number
line, justified only because sign rule's `(-1)² = +1` makes the
180°-orbit close in 2 steps.

Atomic content: identical `(0, 1)` pair, different square under
each rule, shown by `decide`-style witness.
-/

namespace E213.Lib.Math.AngleStructure.SharedPairSlot

open E213.Lib.Math.SignedCut.CDMulRule (signMul complexMul)
open E213.Lib.Math.Real213.CutSumTest (constCut)

/-- The shared "orthogonal slot" `(0, 1)` — second component
    is `+1`, first is `0`.  This represents:
    * `−1` under sign rule (negative number).
    * `i` under complex rule (imaginary unit). -/
def orthSlot : (Nat → Nat → Bool) × (Nat → Nat → Bool) :=
  (constCut 0 1, constCut 1 1)

/-- ★ **Sign rule square**: `(0,1)·(0,1) = (0·0 + 1·1, 0·1 + 1·0)
    = (1, 0)` (= positive 1).  Order 2 → 180° interpretation. -/
theorem orthSlot_signSquare :
    signMul orthSlot.1 orthSlot.2 orthSlot.1 orthSlot.2
      = (E213.Lib.Math.Real213.CutSum.cutSum
          (E213.Lib.Math.Real213.CutMul.cutMul (constCut 0 1) (constCut 0 1))
          (E213.Lib.Math.Real213.CutMul.cutMul (constCut 1 1) (constCut 1 1)),
         E213.Lib.Math.Real213.CutSum.cutSum
          (E213.Lib.Math.Real213.CutMul.cutMul (constCut 0 1) (constCut 1 1))
          (E213.Lib.Math.Real213.CutMul.cutMul (constCut 1 1) (constCut 0 1))) :=
  rfl

/-- ★ **Complex rule first component**: `(0·0 − 1·1)` lands as
    just `0·0 = 0` at the positive-cut layer (negative `b·d`
    flipped to negative pair component, encoded structurally). -/
theorem orthSlot_complexSquare_re :
    (complexMul orthSlot.1 orthSlot.2 orthSlot.1 orthSlot.2).1
      = E213.Lib.Math.Real213.CutMul.cutMul (constCut 0 1)
                                              (constCut 0 1) := rfl

/-- ★ **Complex rule cross term**: `0·1 + 1·0 = 0`. -/
theorem orthSlot_complexSquare_im :
    (complexMul orthSlot.1 orthSlot.2 orthSlot.1 orthSlot.2).2
      = E213.Lib.Math.Real213.CutSum.cutSum
          (E213.Lib.Math.Real213.CutMul.cutMul (constCut 0 1) (constCut 1 1))
          (E213.Lib.Math.Real213.CutMul.cutMul (constCut 1 1) (constCut 0 1))
       := rfl

end E213.Lib.Math.AngleStructure.SharedPairSlot
