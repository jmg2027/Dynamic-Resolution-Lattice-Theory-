import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain

/-!
# The cubic character commutes with conjugation — `(ᾱ/d)₃ = conj (α/d)₃` (∅-axiom)

★★★★ `char_conj` : the cubic character `χ(α) = α^m` intertwines with complex conjugation,

  `χ(ᾱ) = conj χ(α)`,  i.e.  `(ᾱ/d)₃ = conj (α/d)₃`.

Since conjugation swaps the two non-trivial cube roots of unity (`conj ω = ω²`), this is the structural
identity that pairs `(α/d)₃` with `(ᾱ/d)₃` — the reflection underlying the symmetry of cubic
reciprocity (`χ(ᾱ)` and the conjugate prime `d̄`).  The character is built from `pow` and `conj` is a
ring homomorphism (`conj_mul`), so the relation is a clean induction.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharConj

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow one pow_succ pow_zero)

/-- ★★★★ **The cubic character commutes with conjugation** — `χ(ᾱ) = conj χ(α)`, i.e.
    `(ᾱ)^m = conj (α^m)`.  By induction: the `n+1` step is `conj(α^n)·ᾱ = conj(α^n · α)` via the
    homomorphism `conj_mul` (`ℤ[ω]` commutative).  ∅-axiom. -/
theorem char_conj (α : ZOmega) : ∀ n : Nat, pow (conj α) n = conj (pow α n)
  | 0 => by show one = conj one; decide
  | n + 1 => by
      show pow (conj α) n * conj α = conj (pow α n * α)
      rw [char_conj α n, conj_mul]

/-- ★★★ **The cubic character of the conjugate is the conjugate value** (the `m`-power instance of
    `char_conj`): `(ᾱ/d)₃ = conj (α/d)₃`.  With `conj ω = ω²` this pairs the character of `α` with that
    of `ᾱ`. -/
theorem char_conj_value (α : ZOmega) (m : Nat) : pow (conj α) m = conj (pow α m) :=
  char_conj α m

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharConj
