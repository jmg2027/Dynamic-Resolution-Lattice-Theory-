import E213.Lib.Math.SignedCut.Core
import E213.Lib.Math.SignedCut.Algebra
import E213.Lib.Math.SignedCut.GenericGeomBridge

/-!
# SignedCut — Capstone synthesis (∅-axiom)

4 cluster witnesses + total bundle.  Closes residual from
PR #59: generic-`x` cutInv bridge requiring cutSub-equivalent.

213-native paradigm: signed `Cut` = `(positive, negative)` pair
(Cayley-Dickson level-0 sign extension), structurally
mirroring `ComplexCut := (re, im)`.
-/

namespace E213.Lib.Math.SignedCut.Capstone

open E213.Lib.Math.SignedCut.Core
  (SignedCut zero one negOne pos neg signedNeg signedAdd
   signedSub signedMul)
open E213.Lib.Math.SignedCut.Algebra
  (signedNeg_involutive signedNeg_one signedSub_self
   signedAdd_zero_right)
open E213.Lib.Math.SignedCut.GenericGeomBridge
  (oneMinus oneMinus_pos oneMinus_neg signedGeom_recurrence)
open E213.Lib.Math.Real213.CutSum (cutSum)
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Real213.CutLogODE (geomPartialSum)

/-- ★ **Algebra witness**. -/
theorem algebra_witness (s : SignedCut) :
    signedNeg (signedNeg s) = s
    ∧ signedNeg one = negOne :=
  ⟨signedNeg_involutive s, signedNeg_one⟩

/-- ★ **`oneMinus x` witness**. -/
theorem oneMinus_witness (x : Nat → Nat → Bool) :
    pos (oneMinus x) = cutSum (constCut 1 1) (constCut 0 1)
    ∧ neg (oneMinus x) = cutSum (constCut 0 1) x :=
  ⟨oneMinus_pos x, oneMinus_neg x⟩

/-- ★ **Generic-x fixpoint witness**. -/
theorem fixpoint_witness (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x 0 = constCut 0 1
    ∧ geomPartialSum x (N + 1)
        = cutSum (geomPartialSum x N)
            (E213.Lib.Math.Real213.CutPow.cutPow x N)
    ∧ pos (oneMinus x) = cutSum (constCut 1 1) (constCut 0 1) :=
  ⟨rfl, signedGeom_recurrence x N, oneMinus_pos x⟩

/-- ★★★ **Total witness** ★★★. -/
theorem total_witness (s : SignedCut) (x : Nat → Nat → Bool) (N : Nat) :
    signedNeg (signedNeg s) = s
    ∧ signedNeg one = negOne
    ∧ pos (oneMinus x) = cutSum (constCut 1 1) (constCut 0 1)
    ∧ geomPartialSum x (N + 1)
        = cutSum (geomPartialSum x N)
            (E213.Lib.Math.Real213.CutPow.cutPow x N) :=
  ⟨signedNeg_involutive s, signedNeg_one,
   oneMinus_pos x, signedGeom_recurrence x N⟩

end E213.Lib.Math.SignedCut.Capstone
