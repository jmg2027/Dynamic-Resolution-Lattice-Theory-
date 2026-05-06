import E213.Meta.UniversalLens.Core
import E213.Meta.UniversalLens.Nat2
import E213.Meta.UniversalLens.Nat2Inj

/-!
# Universal Lens at ℕ³ — triple-codomain universality

Extends `expSumLens : Lens (ℕ × ℕ)` to `expSumLens3 : Lens (ℕ³)` by
adding a third independent component (leaves count).  The first
component re-uses the bit-pattern encoding `2^x + 2^y`, the second
re-uses depth, and the third is the leaves catamorphism.

Triple-codomain demonstrates: **adding components to a universal
lens preserves universality**.  In particular, the bit-pattern
component is sufficient to inject Raw into any product type whose
first projection is the exp-sum encoding.

Closes part of HANDOFF Open Continuation #5 (Universal Lens at
higher codomains).
-/

namespace E213.Meta.UniversalLens.Nat3

open E213.Theory E213.Lens
open E213.Meta.UniversalLens.Nat2Inj (expSumNat expSumNat_slash expSumNat_inj)

/-- Lens at ℕ³ = ℕ × (ℕ × ℕ).  Three independent encodings:
    - 1st: bit-pattern `2^x.1 + 2^y.1` (universal injector)
    - 2nd: depth counter `x.2.1 + y.2.1 + 1`
    - 3rd: leaves count `x.2.2 + y.2.2` (base 1 ⇒ # of leaves) -/
def expSumLens3 : Lens (Nat × Nat × Nat) where
  base_a := (1, 0, 1)
  base_b := (2, 0, 1)
  combine x y :=
    (2^x.1 + 2^y.1, x.2.1 + y.2.1 + 1, x.2.2 + y.2.2)

/-- Combine is symmetric (componentwise).  STRICT ∅-AXIOM. -/
theorem expSumLens3_symmetric :
    ∀ u v : Nat × Nat × Nat,
      expSumLens3.combine u v = expSumLens3.combine v u := by
  intro u v
  show (2^u.1 + 2^v.1, u.2.1 + v.2.1 + 1, u.2.2 + v.2.2)
      = (2^v.1 + 2^u.1, v.2.1 + u.2.1 + 1, v.2.2 + u.2.2)
  congr 1
  · exact Nat.add_comm _ _
  congr 1
  · congr 1; exact Nat.add_comm _ _
  · exact Nat.add_comm _ _

/-- Concrete: view a = (1, 0, 1). -/
theorem expSumLens3_view_a : expSumLens3.view Raw.a = (1, 0, 1) := rfl

/-- Concrete: view b = (2, 0, 1). -/
theorem expSumLens3_view_b : expSumLens3.view Raw.b = (2, 0, 1) := rfl

/-- Sample: view (slash a b) = (6, 1, 2). -/
example : expSumLens3.view (Raw.slash Raw.a Raw.b (by decide))
        = (6, 1, 2) := by decide

/-- ★★★ Projection lemma: 1st component = expSumNat (proved by
    structural induction on Raw, using combine separability). -/
theorem expSumLens3_view_fst (r : Raw) :
    (expSumLens3.view r).1 = expSumNat r := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
    have hfs : expSumLens3.view (Raw.slash x y h)
                = expSumLens3.combine
                    (expSumLens3.view x) (expSumLens3.view y) :=
      Raw.fold_slash _ _ _ expSumLens3_symmetric x y h
    rw [hfs, expSumNat_slash _ _ h]
    show 2^(expSumLens3.view x).1 + 2^(expSumLens3.view y).1
       = 2^(expSumNat x) + 2^(expSumNat y)
    rw [ihx, ihy]

/-- ★★★★★★★★ FULL injectivity of expSumLens3.view (full universality
    at ℕ³).  Strategy: project to first component, lift to expSumNat
    (proved injective in `UniversalLensNat2Inj`). -/
theorem expSumLens3_view_inj : Function.Injective expSumLens3.view := by
  intro r s hrs
  apply expSumNat_inj
  rw [← expSumLens3_view_fst r, ← expSumLens3_view_fst s, hrs]

/-- ★★★★★★★★★ expSumLens3 is a Universal Lens at ℕ³ codomain. -/
theorem expSumLens3_is_universal :
    E213.Meta.UniversalLens.Core.IsUniversal expSumLens3 :=
  expSumLens3_view_inj

end E213.Meta.UniversalLens.Nat3
