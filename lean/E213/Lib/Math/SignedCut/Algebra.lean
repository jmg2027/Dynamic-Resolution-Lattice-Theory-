import E213.Lib.Math.SignedCut.Core

/-!
# SignedCut — algebraic identities (∅-axiom)

Group structure on `SignedCut` via the pair representation.

Atomic content:
  * `signedNeg` is involutive (rfl): `−(−s) = s`.
  * `signedSub s s = (a + b, b + a)` — sub-self gives a balanced pair.
  * Identity element behaviors of `zero`, `one`, `negOne`.
-/

namespace E213.Lib.Math.SignedCut.Algebra

open E213.Lib.Math.SignedCut.Core
  (SignedCut zero one negOne ofPos ofNeg pos neg
   signedNeg signedAdd signedSub signedMul)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- ★ **Negation is involutive** (rfl). -/
theorem signedNeg_involutive (s : SignedCut) :
    signedNeg (signedNeg s) = s := rfl

/-- ★ **`−zero = zero`** (rfl since pair (0,0) flipped is (0,0)). -/
theorem signedNeg_zero : signedNeg zero = zero := rfl

/-- ★ **`−one = negOne`** (rfl). -/
theorem signedNeg_one : signedNeg one = negOne := rfl

/-- ★ **`−negOne = one`** (rfl). -/
theorem signedNeg_negOne : signedNeg negOne = one := rfl

/-- ★ **`pos zero = 0`, `neg zero = 0`** (rfl). -/
theorem zero_components :
    pos zero = constCut 0 1 ∧ neg zero = constCut 0 1 :=
  ⟨rfl, rfl⟩

/-- ★ **`pos one = 1`, `neg one = 0`** (rfl). -/
theorem one_components :
    pos one = constCut 1 1 ∧ neg one = constCut 0 1 :=
  ⟨rfl, rfl⟩

/-- ★ **`pos negOne = 0`, `neg negOne = 1`** (rfl). -/
theorem negOne_components :
    pos negOne = constCut 0 1 ∧ neg negOne = constCut 1 1 :=
  ⟨rfl, rfl⟩

/-- ★ **ofPos / ofNeg components** (rfl). -/
theorem ofPos_neg_components (c : Nat → Nat → Bool) :
    pos (ofPos c) = c
    ∧ neg (ofPos c) = constCut 0 1
    ∧ pos (ofNeg c) = constCut 0 1
    ∧ neg (ofNeg c) = c :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **`signedSub s s` equals `(s.1 + s.2, s.2 + s.1)`**:
    sub-self gives a balanced (`a + b`, `b + a`) pair, which
    represents 0 at the real layer modulo `cutSum` commutativity. -/
theorem signedSub_self (s : SignedCut) :
    signedSub s s
      = (E213.Lib.Math.Real213.Sum.CutSum.cutSum s.1 s.2,
         E213.Lib.Math.Real213.Sum.CutSum.cutSum s.2 s.1) := rfl

/-- ★ **`signedAdd s zero = (s.1 + 0, s.2 + 0)`** (rfl). -/
theorem signedAdd_zero_right (s : SignedCut) :
    signedAdd s zero
      = (E213.Lib.Math.Real213.Sum.CutSum.cutSum s.1 (constCut 0 1),
         E213.Lib.Math.Real213.Sum.CutSum.cutSum s.2 (constCut 0 1)) := rfl

end E213.Lib.Math.SignedCut.Algebra
