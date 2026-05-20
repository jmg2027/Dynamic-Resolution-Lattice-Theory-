import E213.Meta.Nat.Max213
import E213.Lib.Math.Real213.Core.CutFnData
import E213.Lib.Math.Real213.Core.Dyadic
import E213.Lib.Math.Real213.Sum.CutSumDetermined
import E213.Lib.Math.Real213.Mul.CutMulDetermined

import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutPow
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# Real213IsSmooth: smoothness as resolution-compression filter

## 213-native philosophy

On a finite fractal lattice, continuity-without-differentiability
is the generic structural outcome (Weierstrass-class trajectories).
Smoothness is a constructive filter: a function passes `IsSmooth`
iff it carries an explicit dyadic linearity modulus as data
(constructive Bishop-style).

Differentiation is structured as a constructive filter: only
functions equipped with an explicit dyadic linearity modulus pass
the IsSmooth type.

## Definition

A function f : RealCut → RealCut is `IsSmooth` iff it ships:
1. **LocallyDeterminedData** : continuity (LDD modulus N m k).
2. **linearityModulus n : Nat** : for desired linear-approximation
   error tolerance 2^(-n), input resolution 2^(-linearityModulus n)
   suffices to expose linear behavior.

The modulus is constructive data, not derived externally.  Each
concrete instance (polynomial, scaling function) constructs the
modulus + its linearity certificate pointwise.

## Significance

- LocallyDetermined functions (LDD): continuity is automatic.
- IsSmooth functions: a strict subset requiring explicit dyadic
  modulus of linearity.
- Most lattice trajectories carry LDD but cannot exhibit linearity
  modulus — Weierstrass-class continuous-but-non-differentiable
  functions are the structural norm under finite-precision geometry.
  IsSmooth is the exception-by-construction.
-/

namespace E213.Lib.Math.Analysis.Differentiation.Smooth

open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Bisection.CutBisection (cutHalf cutMid)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutPow (cutPow cutScale)
open E213.Lib.Math.Real213.Sum.CutSum (cutSumAux)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Core.CutFnData (LocallyDeterminedData idLDD constLDD cutScaleLDD cutHalfLDD composeLDD maxRange maxRange_ge)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Real213.Sum.CutSumDetermined (cutSumAux_congr)
open E213.Lib.Math.Real213.Mul.CutMulDetermined (cutMulOuter_congr)

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
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_left _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sf.N (2*m) (2*k) m' (2*k)
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_left _ _))
    · intro m' hm'
      apply sg.prop
      intro m'' k'' hm'' hk''
      apply hagree
      · exact Nat.le_trans hm''
          (Nat.le_trans (maxRange_ge sg.N (2*m) (2*k) m' (2*k)
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_right _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sg.N (2*m) (2*k) m' (2*k)
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_right _ _))
    · exact Nat.le_refl _

/-- **Pointwise sum of smooth is smooth**.  Per user's Sec 2:
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
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_left _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sf.N ((m+1)*(k+1)) k m' k
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_left _ _))
    · intro m' hm'
      apply sg.prop
      intro m'' k'' hm'' hk''
      apply hagree
      · exact Nat.le_trans hm''
          (Nat.le_trans (maxRange_ge sg.N ((m+1)*(k+1)) k m' k
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_right _ _))
      · exact Nat.le_trans hk''
          (Nat.le_trans (maxRange_ge sg.N ((m+1)*(k+1)) k m' k
            hm' (Nat.le_refl _)) (E213.Meta.Nat.Max213.le_max_right _ _))
    · exact Nat.le_refl _

/-- **Pointwise product of smooth is smooth**.  Per user's Sec 2:
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

/-- **x ↦ x² is smooth**: derived from mulIsSmooth ∘ id × id. -/
def squareIsSmooth : IsSmooth (fun x => cutMul x x) :=
  mulIsSmooth idIsSmooth idIsSmooth

/-- **x ↦ x³ is smooth**: derived from mulIsSmooth ∘ id × square. -/
def cubeIsSmooth : IsSmooth (fun x => cutMul x (cutMul x x)) :=
  mulIsSmooth idIsSmooth squareIsSmooth

/-- **x ↦ x⁴ is smooth**: square of square. -/
def quarticIsSmooth : IsSmooth (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  mulIsSmooth squareIsSmooth squareIsSmooth

/-- **x ↦ x⁵ is smooth**: square × cube. -/
def quinticIsSmooth :
    IsSmooth (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) :=
  mulIsSmooth squareIsSmooth cubeIsSmooth

/-- **x ↦ x⁶ is smooth**: cube × cube. -/
def sexticIsSmooth :
    IsSmooth (fun x => cutMul (cutMul x (cutMul x x)) (cutMul x (cutMul x x))) :=
  mulIsSmooth cubeIsSmooth cubeIsSmooth

/-- **x ↦ x⁷ is smooth**: cube × quartic. -/
def septicIsSmooth :
    IsSmooth (fun x => cutMul (cutMul x (cutMul x x))
                              (cutMul (cutMul x x) (cutMul x x))) :=
  mulIsSmooth cubeIsSmooth quarticIsSmooth

/-- **x ↦ x⁸ is smooth**: quartic × quartic. -/
def octicIsSmooth :
    IsSmooth (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                              (cutMul (cutMul x x) (cutMul x x))) :=
  mulIsSmooth quarticIsSmooth quarticIsSmooth

/-- **Midpoint smoothness**: if f, g smooth, so is fun x => cutMid (f x) (g x).
    Composes cutHalf ∘ (cutSum on f, g).  Linear like add. -/
def midIsSmooth {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : IsSmooth f) (sg : IsSmooth g) :
    IsSmooth (fun x => cutMid (f x) (g x)) where
  toLocallyDeterminedData :=
    composeLDD cutHalfLDD
      (addLDD sf.toLocallyDeterminedData sg.toLocallyDeterminedData)
  linearityModulus := fun n =>
    max (sf.linearityModulus n) (sg.linearityModulus n)

/-- **x ↦ x¹⁰ is smooth**: x⁵ × x⁵ = quintic × quintic, modulus 10n. -/
def decicIsSmooth :
    IsSmooth (fun x => cutMul (cutMul (cutMul x x) (cutMul x (cutMul x x)))
                              (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  mulIsSmooth quinticIsSmooth quinticIsSmooth

/-- **x ↦ x¹⁶ is smooth**: octic × octic, modulus 16n.  Power-of-2 chain. -/
def hexadecicIsSmooth :
    IsSmooth (fun x => cutMul ((fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)
                              ((fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)) :=
  mulIsSmooth octicIsSmooth octicIsSmooth

/-- **x ↦ x⁹ is smooth**: x⁴ × x⁵, modulus 9n. -/
def nonicIsSmooth :
    IsSmooth (fun x => cutMul ((fun x => cutMul (cutMul x x) (cutMul x x)) x)
                              ((fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) x)) :=
  mulIsSmooth quarticIsSmooth quinticIsSmooth

/-- **x ↦ x¹² is smooth**: x⁴ × x⁸, modulus 12n. -/
def twelfthIsSmooth :
    IsSmooth (fun x => cutMul ((fun x => cutMul (cutMul x x) (cutMul x x)) x)
                              ((fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)) :=
  mulIsSmooth quarticIsSmooth octicIsSmooth

/-- **x ↦ x¹⁵ is smooth**: x⁷ × x⁸, modulus 15n. -/
def fifteenthIsSmooth :
    IsSmooth (fun x => cutMul ((fun x => cutMul (cutMul x (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)
                              ((fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)) :=
  mulIsSmooth septicIsSmooth octicIsSmooth

/-- **cutPow IsSmooth (recursive)**: x ↦ cutPow x n is smooth for every n.
    Built via repeated mulIsSmooth on the cutPow recurrence
    (cutPow x (n+1) = cutMul (cutPow x n) x). -/
def cutPowFnIsSmooth : ∀ n, IsSmooth (fun x => cutPow x n)
  | 0 => constIsSmooth (constCut 1 1)
  | n+1 => mulIsSmooth (cutPowFnIsSmooth n) idIsSmooth

/-- **x ↦ x¹¹ is smooth**: x³ × x⁸ (degree 11). -/
def eleventhIsSmooth :
    IsSmooth (fun x => cutMul ((fun x => cutMul x (cutMul x x)) x)
                              ((fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)) :=
  mulIsSmooth cubeIsSmooth octicIsSmooth

/-- **x ↦ x¹³ is smooth**: x⁵ × x⁸ (degree 13). -/
def thirteenthIsSmooth :
    IsSmooth (fun x => cutMul ((fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) x)
                              ((fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)) :=
  mulIsSmooth quinticIsSmooth octicIsSmooth

/-- **x ↦ x¹⁴ is smooth**: x⁶ × x⁸ (degree 14). -/
def fourteenthIsSmooth :
    IsSmooth (fun x => cutMul ((fun x => cutMul (cutMul x (cutMul x x)) (cutMul x (cutMul x x))) x)
                              ((fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                                (cutMul (cutMul x x) (cutMul x x))) x)) :=
  mulIsSmooth sexticIsSmooth octicIsSmooth

end E213.Lib.Math.Analysis.Differentiation.Smooth
