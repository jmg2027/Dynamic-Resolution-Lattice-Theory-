import E213.Meta.UniversalLens.Padding
import E213.Math.NatHelpers.AddMod213
import E213.Meta.UniversalLens.Nat2
import E213.Meta.UniversalLens.Nat2Inj

/-!
# Universal Lens at ℕ⁴ — quadruple-codomain via padding lemma

Applies the abstract padding lemma `view_inj_of_fst_eq_universal`
to construct a Universal Lens at ℕ⁴ codomain in *minimal proof size*.

Codomain: `ℕ × ℕ × ℕ × ℕ` (= ℕ × (ℕ × (ℕ × ℕ))).
Encodings:
  - 1st: bit-pattern `2^x.1 + 2^y.1` (universal injector)
  - 2nd: depth `x.2.1 + y.2.1 + 1`
  - 3rd: leaves `x.2.2.1 + y.2.2.1`
  - 4th: max-depth `Nat.max x.2.2.2 y.2.2.2 + 1`

The 4th component (max-depth) is independent of leaves and depth —
demonstrates that arbitrary additional readings can be packed
without affecting injectivity.
-/

namespace E213.Meta.UniversalLens.Nat4

open E213.Theory E213.Lens
open E213.Meta.UniversalLens.Nat2Inj (expSumNat expSumNat_slash expSumNat_inj)

abbrev Nat4 : Type := Nat × Nat × Nat × Nat

/-- Lens at ℕ⁴.  4 independent encodings: bit-pattern, depth,
    leaves, max-depth. -/
def expSumLens4 : Lens Nat4 where
  base_a := (1, 0, 1, 0)
  base_b := (2, 0, 1, 0)
  combine x y :=
    (2^x.1 + 2^y.1,
     x.2.1 + y.2.1 + 1,
     x.2.2.1 + y.2.2.1,
     Nat.max x.2.2.2 y.2.2.2 + 1)

/-- Combine is symmetric.  STRICT ∅-AXIOM. -/
theorem expSumLens4_symmetric :
    ∀ u v : Nat4, expSumLens4.combine u v = expSumLens4.combine v u := by
  intro u v
  show (2^u.1 + 2^v.1, u.2.1 + v.2.1 + 1, u.2.2.1 + v.2.2.1,
        Nat.max u.2.2.2 v.2.2.2 + 1)
      = (2^v.1 + 2^u.1, v.2.1 + u.2.1 + 1, v.2.2.1 + u.2.2.1,
         Nat.max v.2.2.2 u.2.2.2 + 1)
  congr 1
  · exact Nat.add_comm _ _
  congr 1
  · congr 1; exact Nat.add_comm _ _
  congr 1
  · exact Nat.add_comm _ _
  · congr 1; exact E213.Math.NatHelpers.AddMod213.max_comm _ _

/-- Concrete: view a = (1, 0, 1, 0). -/
theorem expSumLens4_view_a : expSumLens4.view Raw.a = (1, 0, 1, 0) := rfl

/-- Concrete: view b = (2, 0, 1, 0). -/
theorem expSumLens4_view_b : expSumLens4.view Raw.b = (2, 0, 1, 0) := rfl

/-- ★★★ Projection lemma: 1st component = expSumNat (induction). -/
theorem expSumLens4_view_fst (r : Raw) :
    (expSumLens4.view r).1 = expSumNat r := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
    have hfs : expSumLens4.view (Raw.slash x y h)
                = expSumLens4.combine
                    (expSumLens4.view x) (expSumLens4.view y) :=
      Raw.fold_slash _ _ _ expSumLens4_symmetric x y h
    rw [hfs, expSumNat_slash _ _ h]
    show 2^(expSumLens4.view x).1 + 2^(expSumLens4.view y).1
       = 2^(expSumNat x) + 2^(expSumNat y)
    rw [ihx, ihy]

/-- ★★★★★★★★ FULL universality of expSumLens4 — derived via the
    abstract padding lemma `view_inj_of_inj_proj`.

  This proof is *one line* by leveraging the padding theory.
  Compare to the 100+ LOC induction in `UniversalLensNat2Inj`. -/
theorem expSumLens4_is_universal :
    E213.Meta.UniversalLens.Core.IsUniversal expSumLens4 :=
  E213.Meta.UniversalLens.Padding.view_inj_of_inj_proj
    expSumLens4 Prod.fst expSumNat expSumNat_inj expSumLens4_view_fst

end E213.Meta.UniversalLens.Nat4
