import E213.Research.Real213CutFnData
import E213.Research.Real213Dyadic
import E213.Research.Real213CutSumDetermined
import E213.Research.Real213CutMulDetermined

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

/-- **Linear scaling is smooth**: cutScale a b (i.e., x ↦ (a/b) * x).

    Linear functions have EXACT linear approximation everywhere, so
    the linearity modulus is trivial (id).  This is the simplest
    non-trivial smooth instance: a literal linear function. -/
def cutScaleIsSmooth (a b : Nat) : IsSmooth (cutScale a b) where
  toLocallyDeterminedData := cutScaleLDD a b
  linearityModulus := id

/-- **Halving is smooth**: cutHalf (i.e., x ↦ x/2).
    Same logic as cutScale — exact linear, trivial modulus. -/
def cutHalfIsSmooth : IsSmooth cutHalf where
  toLocallyDeterminedData := cutHalfLDD
  linearityModulus := id

/-- **Pointwise addition LDD**: if f, g are LDD then so is
    fun x => cutSum (f x) (g x).  Uses cutSumAux_congr directly
    with bound 2m for the search range. -/
def addLDD {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : LocallyDeterminedData f)
    (sg : LocallyDeterminedData g) :
    LocallyDeterminedData (fun x => cutSum (f x) (g x)) where
  N := fun m k =>
    max (maxRange sf.N (2*m) (2*k)) (maxRange sg.N (2*m) (2*k))
  prop := by
    intro m k cx cy hagree
    show cutSumAux (f cx) (g cx) k (2*m) (2*m)
       = cutSumAux (f cy) (g cy) k (2*m) (2*m)
    apply cutSumAux_congr
    · intro m' hm'
      apply sf.prop
      intro m'' k'' hm'' hk''
      apply hagree
      · exact Nat.le_trans hm''
          (Nat.le_trans (maxRange_ge sf.N (2*m) (2*k) m' (2*k)
            hm' (Nat.le_refl _)) (Nat.le_max_left _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sf.N (2*m) (2*k) m' (2*k)
            hm' (Nat.le_refl _)) (Nat.le_max_left _ _))
    · intro m' hm'
      apply sg.prop
      intro m'' k'' hm'' hk''
      apply hagree
      · exact Nat.le_trans hm''
          (Nat.le_trans (maxRange_ge sg.N (2*m) (2*k) m' (2*k)
            hm' (Nat.le_refl _)) (Nat.le_max_right _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sg.N (2*m) (2*k) m' (2*k)
            hm' (Nat.le_refl _)) (Nat.le_max_right _ _))
    · exact Nat.le_refl _

/-- **Pointwise sum of smooth is smooth**.  Per user's Phase J Sec 2:
    cutSum is dyadic-lens superposition, so the linearity modulus is
    the max of input moduli (with a single +1 step buffer).

    h(x) = (f x) + (g x) is smooth with linearityModulus =
    max sf.linearityModulus sg.linearityModulus. -/
def addIsSmooth {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : IsSmooth f) (sg : IsSmooth g) :
    IsSmooth (fun x => cutSum (f x) (g x)) where
  toLocallyDeterminedData :=
    addLDD sf.toLocallyDeterminedData sg.toLocallyDeterminedData
  linearityModulus := fun n =>
    max (sf.linearityModulus n) (sg.linearityModulus n)

/-- **Pointwise product LDD**: if f, g are LDD then so is
    fun x => cutMul (f x) (g x).  Uses cutMulOuter_congr with the
    cutMul-locality bound (m+1)*(k+1). -/
def mulLDD {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : LocallyDeterminedData f)
    (sg : LocallyDeterminedData g) :
    LocallyDeterminedData (fun x => cutMul (f x) (g x)) where
  N := fun m k =>
    max (maxRange sf.N ((m+1)*(k+1)) k)
        (maxRange sg.N ((m+1)*(k+1)) k)
  prop := by
    intro m k cx cy hagree
    show cutMulOuter (f cx) (g cx) k m ((m+1)*(k+1)) ((m+1)*(k+1))
       = cutMulOuter (f cy) (g cy) k m ((m+1)*(k+1)) ((m+1)*(k+1))
    apply cutMulOuter_congr
    · intro m' hm'
      apply sf.prop
      intro m'' k'' hm'' hk''
      apply hagree
      · exact Nat.le_trans hm''
          (Nat.le_trans (maxRange_ge sf.N ((m+1)*(k+1)) k m' k
            hm' (Nat.le_refl _)) (Nat.le_max_left _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sf.N ((m+1)*(k+1)) k m' k
            hm' (Nat.le_refl _)) (Nat.le_max_left _ _))
    · intro m' hm'
      apply sg.prop
      intro m'' k'' hm'' hk''
      apply hagree
      · exact Nat.le_trans hm''
          (Nat.le_trans (maxRange_ge sg.N ((m+1)*(k+1)) k m' k
            hm' (Nat.le_refl _)) (Nat.le_max_right _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sg.N ((m+1)*(k+1)) k m' k
            hm' (Nat.le_refl _)) (Nat.le_max_right _ _))
    · exact Nat.le_refl _

/-- **Pointwise product of smooth is smooth**.  Per user's Phase J Sec 2:
    cutMul has nonlinear error compound from input dynamic range.
    Linearity modulus = sum of input moduli (errors add multiplicatively
    in product, additively in log-form moduli).

    h(x) = (f x) * (g x) is smooth with linearityModulus =
    sf.linearityModulus + sg.linearityModulus. -/
def mulIsSmooth {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : IsSmooth f) (sg : IsSmooth g) :
    IsSmooth (fun x => cutMul (f x) (g x)) where
  toLocallyDeterminedData :=
    mulLDD sf.toLocallyDeterminedData sg.toLocallyDeterminedData
  linearityModulus := fun n =>
    sf.linearityModulus n + sg.linearityModulus n

end E213.Research.Real213CutSum
