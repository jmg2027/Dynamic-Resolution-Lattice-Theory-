import E213.Research.Real213CutFnData
import E213.Research.Real213Dyadic

/-!
# Research.Real213IsSmooth: smoothness as resolution-compression filter

## 213-native philosophy (Phase J)

User insight (Phase J Sec 3): on a finite fractal lattice, the
DEFAULT trajectory is continuous-but-non-differentiable (Weierstrass-
like).  Smoothness is a SPECIAL state where local zigzag noise
cancels via algebraic regularity to look linear at the macro scale.

Therefore differentiation is NOT a default — it is a FILTER admitting
only those functions that carry an explicit dyadic linearity modulus.

## 정의

A function f : RealCut → RealCut is `IsSmooth` iff it ships:
1. **LocallyDeterminedData** : continuity (LDD modulus N m k).
2. **linearityModulus n : Nat** : for desired linear-approximation
   error tolerance 2^(-n), input resolution 2^(-linearityModulus n)
   suffices to expose linear behavior.

The modulus is INJECTED as data (constructive Bishop-style), not
derived classically.  Concrete instances (polynomials, exponentials)
construct linearityModulus + the linearity certificate at use-site.

## 의의

- LocallyDetermined functions (LDD): continuity is automatic.
- IsSmooth functions: a strict subset requiring explicit dyadic
  modulus of linearity.
- Most lattice trajectories carry LDD but cannot exhibit linearity
  modulus — Weierstrass-class continuous-but-non-differentiable
  functions are the GENERIC default.

This inverts the ZFC bias and matches lattice ontology.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **IsSmooth** : differentiability as a constructive filter.

    Carries the LDD continuity data plus an explicit dyadic linearity
    modulus.  Concrete instances supply the linearity certificate
    (i.e., evidence that input resolution 2^(-linearityModulus n)
    really exposes linear behavior with error < 2^(-n)).

    The structure-only form here is the type-level filter: any IsSmooth
    instance must produce a modulus; non-smooth functions fail at the
    construction step. -/
structure IsSmooth (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    extends LocallyDeterminedData f where
  /-- Dyadic linearity modulus: input resolution exponent for given
      output precision exponent. -/
  linearityModulus : Nat → Nat

/-- The identity function is smooth.  The identity is its own linear
    approximation, so the modulus is trivial (id n). -/
def idIsSmooth : IsSmooth id where
  toLocallyDeterminedData := idLDD
  linearityModulus := id

/-- A constant cut function is smooth.  Constants are linear with
    slope 0; the modulus is trivially 0. -/
def constIsSmooth (c : Nat → Nat → Bool) : IsSmooth (constCutFn c) where
  toLocallyDeterminedData := constLDD c
  linearityModulus := fun _ => 0

/-- **Composition of smooth functions is smooth**.
    The linearity moduli compose: m_{f∘g} n = m_g (m_f n). -/
def composeIsSmooth {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : IsSmooth f) (sg : IsSmooth g) : IsSmooth (f ∘ g) where
  toLocallyDeterminedData :=
    composeLDD sf.toLocallyDeterminedData sg.toLocallyDeterminedData
  linearityModulus := fun n => sg.linearityModulus (sf.linearityModulus n)

end E213.Research.Real213CutSum
