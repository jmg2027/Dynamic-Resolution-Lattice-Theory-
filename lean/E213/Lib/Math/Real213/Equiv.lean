import E213.Lib.Math.NatHelpers.Max213
import E213.Lib.Math.Real213.Core

/-!
# Equiv: equivalence properties of Real213.equiv (D3-A)

D3-A first step from `D3_real213_native_R.md` — verifying that the
equiv relation on Real213 is a *genuine* equivalence (reflexive,
symmetric, transitive).

## Significance

`Real213` is the native ℝ of the framework.  Verifying that equiv on
it is an equivalence relation is the first step of *basic algebraic
structure*.

(Other steps of D3-A: framework-internal definitions of addition,
multiplication, etc. — separate work.)
-/

namespace E213.Lib.Math.Real213.Equiv

open E213.Theory E213.Lens
open E213.Lib.Math.Modulus.HasModulus
open E213.Lib.Math.Real213.Core (Real213)

/-- reflexivity of equiv. -/
theorem equiv_refl (r : Real213) : Real213.equiv r r := by
  intro m k _
  exact ⟨0, fun _ _ => rfl⟩

/-- symmetry of equiv. -/
theorem equiv_symm (r r' : Real213) :
    Real213.equiv r r' → Real213.equiv r' r := by
  intro h m k hk
  obtain ⟨N, hN⟩ := h m k hk
  exact ⟨N, fun i hi => (hN i hi).symm⟩

/-- transitivity of equiv. -/
theorem equiv_trans (r r' r'' : Real213) :
    Real213.equiv r r' → Real213.equiv r' r'' → Real213.equiv r r'' := by
  intro h1 h2 m k hk
  obtain ⟨N1, h1N⟩ := h1 m k hk
  obtain ⟨N2, h2N⟩ := h2 m k hk
  refine ⟨max N1 N2, fun i hi => ?_⟩
  have hi1 : i ≥ N1 := Nat.le_trans (E213.Lib.Math.NatHelpers.Max213.le_max_left N1 N2) hi
  have hi2 : i ≥ N2 := Nat.le_trans (E213.Lib.Math.NatHelpers.Max213.le_max_right N1 N2) hi
  exact (h1N i hi1).trans (h2N i hi2)

/-- Setoid instance for Real213 — typeclass form of equivalence properties. -/
instance setoid : Setoid Real213 where
  r := Real213.equiv
  iseqv :=
    { refl := equiv_refl
      symm := fun {x y} => equiv_symm x y
      trans := fun {x y z} => equiv_trans x y z }

end E213.Lib.Math.Real213.Equiv
