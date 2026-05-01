import E213.Research.Real213.IntegralGeneralInt

/-!
# Research.Real213IntegralDyadic

Phase DF: ★★ integration over arbitrary dyadic interval ★★

For any dyadic bracket [numA/2^E, numB/2^E] (numA ≤ numB), the
integral of constant 1 (via id antiderivative) equals (numB - numA)/2^E
cohomologically.

  dyadicIntervalAB numA numB E h  : bracket at any depth E
  integral_one_dyadic              : ∀ E, ∫_a^b 1 dx via id [propEq]

This covers ALL definite integrals of constant 1 over any dyadic
endpoint interval — the most general FTC propEq we can achieve
within the polynomial chain at this point.
-/

namespace E213.Research.Real213.IntegralDyadic

open E213.Firmware E213.Hypervisor

/-- ★ Arbitrary dyadic bracket [numA/2^E, numB/2^E]. -/
def dyadicIntervalAB (numA numB E : Nat) (h : numA ≤ numB) : DyadicBracket where
  numA := numA
  numB := numB
  expE := E
  hLe := h

/-- ★ leftCut at any depth E. -/
theorem dyadicIntervalAB_leftCut (numA numB E : Nat) (h : numA ≤ numB) :
    (dyadicIntervalAB numA numB E h).leftCut = constCut numA (2^E) := rfl

/-- ★ rightCut at any depth E. -/
theorem dyadicIntervalAB_rightCut (numA numB E : Nat) (h : numA ≤ numB) :
    (dyadicIntervalAB numA numB E h).rightCut = constCut numB (2^E) := rfl

/-- ★ fluxAlong id over arbitrary dyadic interval. -/
theorem fluxAlong_id_dyadicAB (numA numB E : Nat) (h : numA ≤ numB) :
    FluxCut.fluxAlong id (dyadicIntervalAB numA numB E h)
      = { forward := constCut numB (2^E),
          backward := constCut numA (2^E) } := rfl

/-- ★★ Integral of constant 1 over any dyadic interval [a/2^E, b/2^E]. -/
theorem integral_one_dyadic (numA numB E : Nat) (h : numA ≤ numB) :
    IsAntiderivative.integral IsAntiderivative.id_anti
        (dyadicIntervalAB numA numB E h)
      = { forward := constCut numB (2^E),
          backward := constCut numA (2^E) } := rfl

/-- Phase DF capstone: most general dyadic FTC propEq. -/
theorem integral_dyadic_capstone (numA numB E : Nat) (h : numA ≤ numB) :
    -- (1) Bracket structure
    (dyadicIntervalAB numA numB E h).numA = numA
    -- (2) numB
    ∧ (dyadicIntervalAB numA numB E h).numB = numB
    -- (3) Endpoint cuts at depth E
    ∧ (dyadicIntervalAB numA numB E h).leftCut = constCut numA (2^E)
    ∧ (dyadicIntervalAB numA numB E h).rightCut = constCut numB (2^E)
    -- (4) ★★ Universal FTC: ∫_(a/2^E)^(b/2^E) 1 dx via id propEq
    ∧ IsAntiderivative.integral IsAntiderivative.id_anti
        (dyadicIntervalAB numA numB E h)
        = { forward := constCut numB (2^E),
            backward := constCut numA (2^E) } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end E213.Research.Real213.IntegralDyadic
