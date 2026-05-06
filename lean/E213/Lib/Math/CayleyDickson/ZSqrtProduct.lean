import E213.Theory.Raw
import E213.Lens.LensCore
import E213.Lens.Characterisation.Catalog
import E213.Lib.Math.CayleyDickson.ZSqrt
import E213.Lib.Math.CayleyDickson.ZSqrtDomain
import E213.Meta.SelfRecognising
import E213.Prelude

/-!
# product codomain `ZSqrt D₁ × ZSqrt D₂`

A deliberate R4-holds / R3-fails witness.

With componentwise multiplication and conjugation, the product
of two `ZSqrt` codomains satisfies R2 (commutative combine)
and a componentwise R4 (swap-matching with componentwise
conj), but **fails R3** because
`(I, 0) * (0, I) = (0, 0)` — a product-of-rings always has
zero divisors.

This is a qualitatively distinct R3-failure from
`ZMod6Lens` (where the base ring itself has zero divisors
via the composite modulus `6`).  Here, the R4-structure is
*preserved* across the product; only the no-zero-divisor
clause breaks.

Relevance to Paper 2 §4: the R4 condition alone does not
prevent zero divisors; R3 is an independent constraint on
the codomain ring.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtProduct


open E213.Lib.Math.CayleyDickson.ZSqrt
open E213.Lib.Math.CayleyDickson.ZSqrt.ZSqrt
open E213.Theory E213.Lens E213.Meta.SelfRecognising
open E213.Lens.Characterisation.Catalog (SwapMatching NonVanishing)

variable {D₁ D₂ : Int}

instance : Zero (ZSqrt D₁ × ZSqrt D₂) := ⟨(0, 0)⟩

/-- Product Lens: componentwise base values and combine. -/
def zSqrtProdLens (D₁ D₂ : Int) :
    Lens (ZSqrt D₁ × ZSqrt D₂) where
  base_a  := (ZSqrt.I,    ZSqrt.I)
  base_b  := (ZSqrt.negI, ZSqrt.negI)
  combine := fun p q => (p.1 * q.1, p.2 * q.2)

/-- Componentwise conjugation. -/
def zSqrtProdConj (p : ZSqrt D₁ × ZSqrt D₂) : ZSqrt D₁ × ZSqrt D₂ :=
  (ZSqrt.conj p.1, ZSqrt.conj p.2)

open E213.Theory E213.Lens E213.Meta.SelfRecognising
open E213.Lens.Characterisation.Catalog (SwapMatching NonVanishing)

-- ═══ R4 (SwapMatching) HOLDS ═══

/-- `zSqrtProdConj` is an involution (componentwise). -/
theorem zSqrtProdConj_involution (p : ZSqrt D₁ × ZSqrt D₂) :
    zSqrtProdConj (zSqrtProdConj p) = p := by
  show (ZSqrt.conj (ZSqrt.conj p.1),
        ZSqrt.conj (ZSqrt.conj p.2)) = p
  rw [ZSqrt.conj_conj, ZSqrt.conj_conj]

theorem zSqrtProdConj_ne_id :
    (zSqrtProdConj : ZSqrt D₁ × ZSqrt D₂ → _) ≠ id := by
  intro h
  have := congrFun h (ZSqrt.I, ZSqrt.I)
  have hfst : (ZSqrt.conj (ZSqrt.I : ZSqrt D₁)) = ZSqrt.I :=
    (Prod.mk.injEq ..).mp this |>.1
  rw [ZSqrt.conj_I] at hfst
  have : (⟨0, -1⟩ : ZSqrt D₁) = ⟨0, 1⟩ := hfst
  have : (-1 : Int) = 1 := (ZSqrt.mk.injEq ..).mp this |>.2
  exact absurd this (by decide)

/-- R4 (SwapMatching) for the product Lens. -/
theorem zSqrtProdLens_R4 :
    SwapMatching (zSqrtProdLens D₁ D₂) zSqrtProdConj := by
  refine ⟨zSqrtProdConj_involution, zSqrtProdConj_ne_id, ?_⟩
  intro r
  show Raw.fold (ZSqrt.I, ZSqrt.I) (ZSqrt.negI, ZSqrt.negI)
        (fun p q => (p.1 * q.1, p.2 * q.2)) (Raw.swap r)
     = zSqrtProdConj (Raw.fold (ZSqrt.I, ZSqrt.I)
        (ZSqrt.negI, ZSqrt.negI)
        (fun p q => (p.1 * q.1, p.2 * q.2)) r)
  exact Raw.fold_swap_hom _ _ _ zSqrtProdConj
    (by show (ZSqrt.conj ZSqrt.I, ZSqrt.conj ZSqrt.I)
          = (ZSqrt.negI, ZSqrt.negI)
        simp only [ZSqrt.conj_I])
    (by show (ZSqrt.conj ZSqrt.negI, ZSqrt.conj ZSqrt.negI)
          = (ZSqrt.I, ZSqrt.I)
        simp only [ZSqrt.conj_negI])
    (fun u v => by
      show (ZSqrt.conj (u.1 * v.1), ZSqrt.conj (u.2 * v.2))
         = ((ZSqrt.conj u.1) * (ZSqrt.conj v.1),
            (ZSqrt.conj u.2) * (ZSqrt.conj v.2))
      simp only [ZSqrt.conj_mul])
    (fun u v => by
      show (u.1 * v.1, u.2 * v.2) = (v.1 * u.1, v.2 * u.2)
      rw [ZSqrt.mul_comm u.1 v.1, ZSqrt.mul_comm u.2 v.2]) r

open E213.Theory E213.Lens E213.Meta.SelfRecognising
open E213.Lens.Characterisation.Catalog (SwapMatching NonVanishing)

-- ═══ R3 FAILS on the product ═══

/-- `(I, 0)` is a valid (nonzero) element of the product. -/
def zSqrtProdLens_I0 : ZSqrt D₁ × ZSqrt D₂ := (ZSqrt.I, 0)

/-- `(0, I)` is a valid (nonzero) element of the product. -/
def zSqrtProdLens_0I : ZSqrt D₁ × ZSqrt D₂ := (0, ZSqrt.I)

/-- **R3 (NonVanishing) FAILS for the product Lens.**
    `(I, 0) * (0, I) = (0, 0)` componentwise even though
    neither factor is zero. -/
theorem zSqrtProdLens_R3_fails :
    ¬ NonVanishing (zSqrtProdLens D₁ D₂) := by
  intro h
  have hnz1 : (zSqrtProdLens_I0 : ZSqrt D₁ × ZSqrt D₂) ≠ 0 := by
    intro heq
    have hfst : (ZSqrt.I : ZSqrt D₁) = 0 :=
      (Prod.mk.injEq ..).mp heq |>.1
    have : (⟨0, 1⟩ : ZSqrt D₁) = ⟨0, 0⟩ := hfst
    have : (1 : Int) = 0 := (ZSqrt.mk.injEq ..).mp this |>.2
    exact absurd this (by decide)
  have hnz2 : (zSqrtProdLens_0I : ZSqrt D₁ × ZSqrt D₂) ≠ 0 := by
    intro heq
    have hsnd : (ZSqrt.I : ZSqrt D₂) = 0 :=
      (Prod.mk.injEq ..).mp heq |>.2
    have : (⟨0, 1⟩ : ZSqrt D₂) = ⟨0, 0⟩ := hsnd
    have : (1 : Int) = 0 := (ZSqrt.mk.injEq ..).mp this |>.2
    exact absurd this (by decide)
  have hne :
      (zSqrtProdLens D₁ D₂).combine zSqrtProdLens_I0 zSqrtProdLens_0I ≠ 0 :=
    h zSqrtProdLens_I0 zSqrtProdLens_0I hnz1 hnz2
  apply hne
  show ((ZSqrt.I : ZSqrt D₁) * 0, (0 : ZSqrt D₂) * ZSqrt.I) = 0
  apply Prod.mk.injEq .. |>.mpr
  refine ⟨?_, ?_⟩
  · show ZSqrt.mul ZSqrt.I 0 = 0
    apply ZSqrt.ext
    · show (0 : Int) * 0 - D₁ * (1 * 0) = 0; simp
    · show (0 : Int) * 0 + 1 * 0 = 0; simp
  · show ZSqrt.mul 0 ZSqrt.I = 0
    apply ZSqrt.ext
    · show (0 : Int) * 0 - D₂ * (0 * 1) = 0; simp
    · show (0 : Int) * 1 + 0 * 0 = 0; simp

end E213.Lib.Math.CayleyDickson.ZSqrtProduct
