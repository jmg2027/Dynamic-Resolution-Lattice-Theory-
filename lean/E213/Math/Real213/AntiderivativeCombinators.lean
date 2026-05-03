import E213.Math.Real213.Antiderivative

/-!
# Research.Real213AntiderivativeCombinators

Phase CO: ★ antiderivative class combinators ★

If F is antiderivative of f, G of g, then:
  mid(F, G) is antiderivative of mid(f, g)
  cutSum(F, G) is antiderivative of cutSum(f, g) [via addIsDifferentiable]

Composition (F ∘ G) is antiderivative of (F'∘G) · G' (chain rule
INVERSE direction — not quite as clean).
-/

namespace E213.Math.Real213.AntiderivativeCombinators

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.Antiderivative (IsAntiderivative)
open E213.Math.Real213.Antiderivative.IsAntiderivative (id_anti)

namespace IsAntiderivative

/-- ★ midpoint combinator: mid(F, G) is antiderivative of mid(f, g). -/
def mid_anti {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g) :
    IsAntiderivative (fun x => cutMid (F x) (G x))
                      (midIsDifferentiable sF sG)
                      (fun x => cutMid (f x) (g x)) :=
  { eq := by
      show (fun x => cutMid (sF.derivative x) (sG.derivative x))
           = (fun x => cutMid (f x) (g x))
      rw [hF.eq, hG.eq] }

/-- ★ Sum combinator: F + G is antiderivative of f + g. -/
def add_anti {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g) :
    IsAntiderivative (fun x => cutSum (F x) (G x))
                      (addIsDifferentiable sF sG)
                      (fun x => cutSum (f x) (g x)) :=
  { eq := by
      show (fun x => cutSum (sF.derivative x) (sG.derivative x))
           = (fun x => cutSum (f x) (g x))
      rw [hF.eq, hG.eq] }

/-- mid(id, id) is antiderivative of mid(1, 1) (= 1). -/
def mid_id_id_anti :
    IsAntiderivative (fun x => cutMid x x)
                      (midIsDifferentiable idIsDifferentiable idIsDifferentiable)
                      (fun x => cutMid (constCut 1 1) (constCut 1 1)) :=
  mid_anti id_anti id_anti

/-- Phase CO capstone: antiderivative combinators yield new instances. -/
theorem antiderivative_combinators_capstone :
    -- (1) mid combinator works (function equality)
    (midIsDifferentiable idIsDifferentiable idIsDifferentiable).derivative
        = (fun x => cutMid (constCut 1 1) (constCut 1 1))
    -- (2) add combinator works
    ∧ (addIsDifferentiable idIsDifferentiable idIsDifferentiable).derivative
        = (fun x => cutSum (constCut 1 1) (constCut 1 1)) :=
  ⟨mid_id_id_anti.eq, (add_anti id_anti id_anti).eq⟩

end IsAntiderivative

end E213.Math.Real213.AntiderivativeCombinators
