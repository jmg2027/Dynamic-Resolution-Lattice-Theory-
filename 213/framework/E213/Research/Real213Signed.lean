import E213.Research.Real213CutMul
import E213.Research.Real213CutSumTest
import E213.Research.Real213CutMulComm

/-!
# Research.Real213Signed: signed Real213 + negation (F3)

`F0_213_native_arithmetic_synthesis.md` 의 F3.  Real213 의 native
form 은 *non-negative* ratios (abLens.view 의 (a, b) 모두 ≥ 0).
음수 표 현 위 해 sign 확장.

## 정의

```
structure SignedCut where
  sign : Bool  -- true = positive, false = negative
  cut : Nat → Nat → Bool  -- absolute value cut
```

Negation = sign flip.

## 의의

- Real213 의 native 가 non-negative — 음수 는 *별 도 layer*.
- 213 axiom 자체 는 a, b 의 *symmetric* 한 두 distinct atom — sign
  은 외부 부착, framework axiom 위 에 layer.
- Bishop 도 signed reals 를 |abs| × sign 으 로 정의.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor
open E213.Research.ArchimedeanCauchy

/-- Signed cut: sign + absolute-value cut. -/
structure SignedCut where
  sign : Bool
  cut : Nat → Nat → Bool

/-- **cutNeg**: sign flip. -/
def cutNeg (s : SignedCut) : SignedCut :=
  { sign := !s.sign, cut := s.cut }

/-- Negation 의 involutivity. -/
theorem cutNeg_cutNeg (s : SignedCut) : cutNeg (cutNeg s) = s := by
  cases s with
  | mk sign cut =>
    cases sign <;> rfl

/-- Sign-aware constant cut. -/
def signedConstCut (sign : Bool) (a b : Nat) : SignedCut :=
  { sign := sign, cut := constCut a b }

/-- Positive 1 의 negation = negative 1. -/
example : cutNeg (signedConstCut true 1 1)
        = signedConstCut false 1 1 := rfl

/-- Negative 1 의 negation = positive 1. -/
example : cutNeg (signedConstCut false 1 1)
        = signedConstCut true 1 1 := rfl

/-- **cutSignedMul**: signed multiplication via |abs| cutMul + sign rule. -/
def cutSignedMul (sx sy : SignedCut) : SignedCut where
  sign := sx.sign == sy.sign
  cut := cutMul sx.cut sy.cut

/-- (+1) * (+1) = (+1).  At cut (1, 1): true. -/
example : (cutSignedMul (signedConstCut true 1 1)
                       (signedConstCut true 1 1)).cut 1 1 = true := by decide

/-- (-1) * (-1) = (+1).  Sign true. -/
example : (cutSignedMul (signedConstCut false 1 1)
                       (signedConstCut false 1 1)).sign = true := by decide

/-- (+1) * (-1) = (-1).  Sign false. -/
example : (cutSignedMul (signedConstCut true 1 1)
                       (signedConstCut false 1 1)).sign = false := by decide

/-- cutNeg of signedConstCut: flips sign. -/
theorem cutNeg_signedConstCut (sign : Bool) (a b : Nat) :
    cutNeg (signedConstCut sign a b) = signedConstCut (!sign) a b := rfl

/-- cutSignedMul commutativity. -/
theorem cutSignedMul_comm (sx sy : SignedCut) :
    cutSignedMul sx sy = cutSignedMul sy sx := by
  show ({ sign := sx.sign == sy.sign, cut := cutMul sx.cut sy.cut } : SignedCut)
     = { sign := sy.sign == sx.sign, cut := cutMul sy.cut sx.cut }
  congr 1
  · cases sx.sign <;> cases sy.sign <;> rfl
  · funext m k; exact cutMul_comm _ _ m k

end E213.Research.Real213CutSum
