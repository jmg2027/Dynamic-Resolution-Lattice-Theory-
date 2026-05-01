import E213.Research.Real213.FluxMVTConcrete

/-!
# Research.Real213FluxFTC

Phase AZ: **Fundamental Theorem of Calculus** in 213-native flux form.

Classical FTC: ∫_a^b f'(x) dx = f(b) - f(a).

213 cohomological reframing: the path-integrated localDivergence
along the bisection of a bracket equals the fluxAlong the bracket
(boundary value).  This is **Stokes' theorem for the dyadic tree**.

  fluxAlong f db                     ←→   f(b) - f(a)  (boundary)
  Σ localDivergence f.deriv along db ←→   ∫_a^b f'    (interior)

The cohomEquiv between these is the FTC.

## Theorems

  ftc_const                : FTC for constant function (trivial)
  ftc_id_unitBracket       : FTC for identity at unitBracket
  fluxAlong_id_unitBracket : id flux gives endpoint pair (0, 1)
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

namespace FluxCut

/-- **fluxAlong id at unitBracket** has endpoints (1, 0). -/
theorem fluxAlong_id_unitBracket :
    fluxAlong id unitBracket
      = { forward := constCut 1 1, backward := constCut 0 1 } := rfl

/-- **FTC for identity at unitBracket**: id.derivative is constant 1,
    so its integral over [0, 1] is 1, matching fluxAlong id = (1, 0). -/
theorem ftc_id_unitBracket :
    fluxAlong id unitBracket = ofCut (constCut 1 1) := rfl

/-- **FTC for constant function**: f(b) - f(a) is balanced (= 0)
    for any constant, matching ∫ 0 dx = 0. -/
theorem ftc_const (c : Nat → Nat → Bool) (db : DyadicBracket) :
    isBalanced (fluxAlong (constCutFn c) db) :=
  fluxAlong_const_isBalanced c db

/-- **FTC bridge for identity**: localDivergence id at unitBracket
    cohomEquiv fluxAlong id at unitBracket.  Both equal (1, 0)
    propositionally (FTC trivial case). -/
theorem ftc_bridge_id_unitBracket :
    localDivergence id unitBracket = fluxAlong id unitBracket := by
  rw [mvt_id_unitBracket, ftc_id_unitBracket]

/-- **FTC for constant**: localDivergence and fluxAlong both balanced. -/
theorem ftc_const_bridge (c : Nat → Nat → Bool) (db : DyadicBracket) :
    isBalanced (localDivergence (constCutFn c) db)
    ∧ isBalanced (fluxAlong (constCutFn c) db) :=
  ⟨localDivergence_const_balanced c db, fluxAlong_const_isBalanced c db⟩

/-- Phase AZ-1 capstone: FTC concrete cases. -/
theorem ftc_concrete_capstone (c : Nat → Nat → Bool) (db : DyadicBracket) :
    -- (1) FTC for id at unit: both sides equal (1, 0)
    fluxAlong id unitBracket = ofCut (constCut 1 1)
    -- (2) FTC bridge: localDivergence id = fluxAlong id at unitBracket
    ∧ localDivergence id unitBracket = fluxAlong id unitBracket
    -- (3) FTC for constant: balanced (zero integral)
    ∧ isBalanced (fluxAlong (constCutFn c) db)
    -- (4) FTC for constant divergence: balanced (zero rate)
    ∧ isBalanced (localDivergence (constCutFn c) db) :=
  ⟨ftc_id_unitBracket, ftc_bridge_id_unitBracket,
   fluxAlong_const_isBalanced c db, localDivergence_const_balanced c db⟩

end FluxCut

end E213.Research.Real213.CutSum
