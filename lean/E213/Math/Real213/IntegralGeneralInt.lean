import E213.Math.Real213.Antiderivative
import E213.Math.Real213.IntegralViaAnti
import E213.Math.Real213.FluxCochain
import E213.Math.Real213.FluxCut
import E213.Math.Real213.DyadicBracket
import E213.Math.Real213.IntegralIntInterval

import E213.Math.Real213.Core
import E213.Math.Real213.CutSumTest
/-!
# Research.Real213IntegralGeneralInt

Phase DE: ★ integration over arbitrary integer interval [a, b] ★

For integers a ≤ b, the bracket [a, b] yields ∫_a^b 1 dx = b - a
cohomologically via id antiderivative.
-/

namespace E213.Math.Real213.IntegralGeneralInt

open E213.Math.Real213.DyadicBracket (DyadicBracket)

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★ General integer interval bracket [a, b] for a ≤ b. -/
def intIntervalAB (a b : Nat) (h : a ≤ b) : DyadicBracket where
  numA := a
  numB := b
  expE := 0
  hLe := h

/-- ★ leftCut of intIntervalAB = constCut a 1. -/
theorem intIntervalAB_leftCut (a b : Nat) (h : a ≤ b) :
    (intIntervalAB a b h).leftCut = constCut a 1 := rfl

/-- ★ rightCut of intIntervalAB = constCut b 1. -/
theorem intIntervalAB_rightCut (a b : Nat) (h : a ≤ b) :
    (intIntervalAB a b h).rightCut = constCut b 1 := rfl

/-- ★ fluxAlong id over [a, b] = (b, a). -/
theorem fluxAlong_id_intIntervalAB (a b : Nat) (h : a ≤ b) :
    E213.Math.Real213.FluxCochain.FluxCut.fluxAlong id (intIntervalAB a b h)
      = { forward := constCut b 1, backward := constCut a 1 } := rfl

/-- ★ Integral of constant 1 over [a, b] via id antiderivative. -/
theorem integral_one_intIntervalAB (a b : Nat) (h : a ≤ b) :
    E213.Math.Real213.IntegralViaAnti.IsAntiderivative.integral E213.Math.Real213.Antiderivative.IsAntiderivative.id_anti (intIntervalAB a b h)
      = { forward := constCut b 1, backward := constCut a 1 } := rfl

/-- ★ Zero-length interval [a, a]: integral balanced. -/
theorem integral_one_intIntervalAA (a : Nat) :
    E213.Math.Real213.IntegralViaAnti.IsAntiderivative.integral E213.Math.Real213.Antiderivative.IsAntiderivative.id_anti
        (intIntervalAB a a (Nat.le_refl a))
      = { forward := constCut a 1, backward := constCut a 1 } := rfl

/-- Phase DE capstone: general integer interval integration. -/
theorem integral_general_int_capstone (a b : Nat) (h : a ≤ b) :
    -- (1) numA = a
    (intIntervalAB a b h).numA = a
    -- (2) numB = b
    ∧ (intIntervalAB a b h).numB = b
    -- (3) leftCut = a
    ∧ (intIntervalAB a b h).leftCut = constCut a 1
    -- (4) rightCut = b
    ∧ (intIntervalAB a b h).rightCut = constCut b 1
    -- (5) ∫_a^b 1 dx via id = (b, a) cohomologically
    ∧ E213.Math.Real213.IntegralViaAnti.IsAntiderivative.integral E213.Math.Real213.Antiderivative.IsAntiderivative.id_anti
        (intIntervalAB a b h)
        = { forward := constCut b 1, backward := constCut a 1 } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end E213.Math.Real213.IntegralGeneralInt
