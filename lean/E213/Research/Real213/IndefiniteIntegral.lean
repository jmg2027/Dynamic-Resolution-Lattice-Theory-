import E213.Research.Real213.NewtonSecond

/-!
# Research.Real213IndefiniteIntegral

Phase DC: ★ indefinite integral as a flux-valued function ★

For F antiderivative of f, the indefinite integral from 0 to x is
F(x) - F(0).  In flux form:
  indefIntFromZero hF x := { forward := F x, backward := F 0 }

This represents ∫_0^x f dt cohomologically.

  indefIntFromZero hF (constCut 1 1) = boundary at x = 1
  indefIntFromZero hF (constCut 0 1) = balanced (= 0)
-/

namespace E213.Research.Real213.IndefiniteIntegral

namespace IsAntiderivative

/-- ★ Indefinite integral from 0 to x via flux. -/
def indefIntFromZero {F sF f} (_hF : IsAntiderivative F sF f)
    (x : Nat → Nat → Bool) : FluxCut :=
  { forward := F x, backward := F (constCut 0 1) }

/-- ★ Indefinite integral at x = 1 of constant 1 (via id_anti) = 1. -/
theorem indefIntFromZero_one_at_one :
    indefIntFromZero id_anti (constCut 1 1) = FluxCut.ofCut (constCut 1 1) :=
  rfl

/-- ★ Indefinite integral at x = 0 is balanced (= 0). -/
theorem indefIntFromZero_at_zero {F sF f} (hF : IsAntiderivative F sF f) :
    (indefIntFromZero hF (constCut 0 1)).forward
      = (indefIntFromZero hF (constCut 0 1)).backward :=
  rfl

/-- ★ Indefinite integral linearity: ∫_0^x (f+g) = (∫_0^x f) + (∫_0^x g). -/
theorem indefIntFromZero_add {F G f g}
    {sF : IsDifferentiable F} {sG : IsDifferentiable G}
    (hF : IsAntiderivative F sF f) (hG : IsAntiderivative G sG g)
    (x : Nat → Nat → Bool) :
    indefIntFromZero (add_anti hF hG) x
      = { forward := cutSum (F x) (G x),
          backward := cutSum (F (constCut 0 1)) (G (constCut 0 1)) } :=
  rfl

end IsAntiderivative

/-- Phase DC capstone: indefinite integral properties. -/
theorem indefIntFromZero_capstone (a : Nat) :
    -- (1) ∫_0^1 1 dx = 1 (id_anti at x = 1)
    IsAntiderivative.indefIntFromZero IsAntiderivative.id_anti
        (constCut 1 1) = FluxCut.ofCut (constCut 1 1)
    -- (2) ∫_0^0 (id_anti) = balanced (zero-length)
    ∧ (IsAntiderivative.indefIntFromZero IsAntiderivative.id_anti
        (constCut 0 1)).forward
        = (IsAntiderivative.indefIntFromZero IsAntiderivative.id_anti
        (constCut 0 1)).backward
    -- (3) ∫_0^1 a (constant a via linear_anti) form
    ∧ IsAntiderivative.indefIntFromZero (linear_anti a 0) (constCut 1 1)
        = { forward := linearWithIntercept a 0 (constCut 1 1),
            backward := linearWithIntercept a 0 (constCut 0 1) } :=
  ⟨IsAntiderivative.indefIntFromZero_one_at_one,
   IsAntiderivative.indefIntFromZero_at_zero IsAntiderivative.id_anti,
   rfl⟩

end E213.Research.Real213.IndefiniteIntegral
