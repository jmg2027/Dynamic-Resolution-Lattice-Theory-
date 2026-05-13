import E213.Lib.Math.Real213.Core.Core.ValidCut
import E213.Lib.Math.Real213.Sum.CutSumOne
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Mul.CutDouble

import E213.Lib.Math.Real213.Core.Core.CutPoset
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# Dyadic: dyadic cuts (denominator = 2^E)

213's universe is a binary tree.  cutMid is a bit-shift, not a
continuous halving.  So the natural cut representation is *dyadic*:
constCut with denominator a power of 2.

This module defines the dyadic structure cleanly and exhibits its
basic properties.  All RatioCut closure issues from the general
case vanish here because constCut is always RatioCut.

## Significance

User insight (): what 213 resisted was the generality of
RatioCut closure — cutSum with arbitrary denominators breaks at the
boundary (tight precision at k1 ≥ 2).  Moving to dyadic makes that
issue vanish naturally.
-/

namespace E213.Lib.Math.Real213.Core.Core.Dyadic

open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Bisection.CutBisection (cutHalf cutHalf_constCut)
open E213.Lib.Math.Real213.Sum.CutSumOne (cutSum_self)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Core.Core.ValidCut (ValidCut RatioCut constCut_valid constCut_ratio)
open E213.Lib.Math.Real213.Mul.CutDouble (cutDouble cutDouble_constCut)

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

/-- **cutSum_self on dyadicCut** (cutEq, PURE): doubling stays dyadic. -/
theorem cutSum_dyadicCut_self (M E : Nat) :
    E213.Lib.Math.Real213.Core.Core.CutPoset.cutEq
      (cutSum (dyadicCut M E) (dyadicCut M E)) (dyadicCut (2 * M) E) :=
  cutSum_self M (2^E)

/-- **cutHalf of dyadicCut** (cutEq, PURE): increments exponent by 1.
    M / 2^E divided by 2 ≡ M / 2^(E+1). -/
theorem cutHalf_dyadicCut (M E : Nat) :
    ∀ m k, cutHalf (dyadicCut M E) m k = dyadicCut M (E+1) m k := by
  intro m k
  show cutHalf (constCut M (2^E)) m k = constCut M (2^(E+1)) m k
  rw [cutHalf_constCut M (2^E) m k]
  show constCut M (2 * 2^E) m k = constCut M (2^(E+1)) m k
  rw [show (2:Nat)^(E+1) = 2 * 2^E from by
    rw [Nat.pow_succ, Nat.mul_comm]]

/-- **cutDouble of dyadicCut** (cutEq, PURE): doubles numerator, exponent unchanged.
    2 * (M / 2^E) ≡ (2*M) / 2^E. -/
theorem cutDouble_dyadicCut (M E : Nat) :
    E213.Lib.Math.Real213.Core.Core.CutPoset.cutEq
      (cutDouble (dyadicCut M E)) (dyadicCut (2 * M) E) :=
  cutDouble_constCut M (2^E)

end E213.Lib.Math.Real213.Core.Core.Dyadic
