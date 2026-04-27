import E213.Research.Real213ValidCut
import E213.Research.Real213CutSumOne

/-!
# Research.Real213Dyadic: dyadic cuts (denominator = 2^E)

213's universe is a binary tree.  cutMid is a bit-shift, not a
continuous halving.  So the natural cut representation is *dyadic*:
constCut with denominator a power of 2.

This module defines the dyadic structure cleanly and exhibits its
basic properties.  All RatioCut closure issues from the general
case vanish here because constCut is always RatioCut.

## 의의

User insight (Phase J): 213 거부했던 것 은 RatioCut closure 의
일반성 — 임의 분모 의 cutSum 이 boundary 에 서 깨짐 (k1 ≥ 2 의
tight precision).  Dyadic 으 로 가 면 그 issue 가 자연 소멸.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **dyadicCut M E**: rational M / 2^E as a 213 cut function.
    Just constCut M (2^E). -/
def dyadicCut (M E : Nat) : Nat → Nat → Bool := constCut M (2^E)

/-- dyadicCut at exponent 0 is just constCut M 1. -/
theorem dyadicCut_zero (M : Nat) :
    dyadicCut M 0 = constCut M 1 := by
  show constCut M (2^0) = constCut M 1
  rfl

/-- dyadicCut is RatioCut (inherits from constCut). -/
theorem dyadicCut_ratio (M E : Nat) : RatioCut (dyadicCut M E) :=
  constCut_ratio M (2^E)

/-- dyadicCut is ValidCut. -/
theorem dyadicCut_valid (M E : Nat) : ValidCut (dyadicCut M E) :=
  constCut_valid M (2^E)

end E213.Research.Real213CutSum
