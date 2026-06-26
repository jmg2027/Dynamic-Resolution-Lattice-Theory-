import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep

/-!
# The ℤ[ω] cubic character splits over the norm — `χ_d(N(π')) = χ_d(π')·χ_d(π̄')` (∅-axiom)

★★★★ `eisChar_norm_split` : the cubic character `χ_d(α) = α^m mod d` (mod the prime `d` of norm `p`,
`m = (p−1)/3`) on the **rational integer** `N(π') = ‖π'‖²` splits as the product of the characters of
`π'` and its conjugate:

  `χ_d(N(π')) ≡ χ_d(π') · χ_d(π̄')   (mod d)`        (`π̄' = conj π'`).

Because `N(π') = π'·π̄'` **as Eisenstein integers** (`mul_conj_self`: `π'·conj π' = ofInt ‖π'‖²`), this is
just the multiplicativity `char_mul` of the ℤ[ω] cubic character applied to `π'·π̄'`.

This is the bridge the cubic-reciprocity `π ↔ π'` transfer needs: it relates the **rational** character of
the norm `N(π')` (which appears as `χ̄(pr)` in `split_conj_residue_relation`) to the **Eisenstein**
residue symbols `χ_d(π') = (π'/π)₃` and `χ_d(π̄') = (π̄'/π)₃`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharNormSplit

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (char_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)

/-- ★★★★ **The ℤ[ω] cubic character splits over the norm** — `χ_d(N(π')) ≡ χ_d(π')·χ_d(π̄') (mod d)`.
    `N(π') = π'·π̄'` as Eisenstein integers (`mul_conj_self`), so this is `char_mul` at `π'·π̄'`.
    ∅-axiom (PURE). -/
theorem eisChar_norm_split {d : ZOmega} (π' : ZOmega) {pr m : Nat}
    (hπ'norm : π'.normSq = (pr : Int)) :
    ModEq d (pow (ofInt ((pr : Nat) : Int)) m) (pow π' m * pow (conj π') m) := by
  have h1 : ofInt ((pr : Nat) : Int) = π' * conj π' := by rw [mul_conj_self π', hπ'norm]
  rw [h1]
  exact char_mul π' (conj π') m

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharNormSplit
