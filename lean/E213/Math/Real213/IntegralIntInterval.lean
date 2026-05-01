import E213.Math.Real213.IndefiniteIntegral

/-!
# Research.Real213IntegralIntInterval

Phase DD: ★ integration over integer intervals [0, n] ★

For a constant function f = 1, the integral over [0, n] equals n.
Via id_anti: F = id, F(n) - F(0) = n - 0 = n.

In flux form: fluxAlong id (bracket [0, n]) = ofCut (constCut n 1).
-/

namespace E213.Math.Real213.IntegralIntInterval

open E213.Firmware E213.Hypervisor

/-- ★ Integer interval bracket [0, n] at depth 0. -/
def intInterval (n : Nat) : DyadicBracket where
  numA := 0
  numB := n
  expE := 0
  hLe := Nat.zero_le n

/-- ★ leftCut of intInterval n = constCut 0 1. -/
theorem intInterval_leftCut (n : Nat) :
    (intInterval n).leftCut = constCut 0 1 := rfl

/-- ★ rightCut of intInterval n = constCut n 1. -/
theorem intInterval_rightCut (n : Nat) :
    (intInterval n).rightCut = constCut n 1 := rfl

/-- ★ fluxAlong id over [0, n] = (n, 0) — boundary value. -/
theorem fluxAlong_id_intInterval (n : Nat) :
    FluxCut.fluxAlong id (intInterval n)
      = { forward := constCut n 1, backward := constCut 0 1 } := rfl

/-- ★ Integral of constant 1 over [0, n] via id antiderivative = n. -/
theorem integral_one_intInterval (n : Nat) :
    IsAntiderivative.integral IsAntiderivative.id_anti (intInterval n)
      = { forward := constCut n 1, backward := constCut 0 1 } := rfl

/-- Phase DD capstone: integration over integer intervals. -/
theorem integral_int_interval_capstone (n : Nat) :
    -- (1) Bracket structure
    (intInterval n).numA = 0
    -- (2) Right endpoint = n
    ∧ (intInterval n).numB = n
    -- (3) leftCut = 0
    ∧ (intInterval n).leftCut = constCut 0 1
    -- (4) rightCut = n
    ∧ (intInterval n).rightCut = constCut n 1
    -- (5) ∫_0^n 1 dx via id = (n, 0) cohomologically
    ∧ IsAntiderivative.integral IsAntiderivative.id_anti (intInterval n)
        = { forward := constCut n 1, backward := constCut 0 1 } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end E213.Math.Real213.IntegralIntInterval
