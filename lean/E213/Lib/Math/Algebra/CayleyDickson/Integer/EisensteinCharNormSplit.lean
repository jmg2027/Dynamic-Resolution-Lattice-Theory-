import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots

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
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (char_mul ofInt_pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (trans symm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega chiOmega_lift)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots (ofInt_natMod_modEq)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar)

/-- ★★★★ **The ℤ[ω] cubic character splits over the norm** — `χ_d(N(π')) ≡ χ_d(π')·χ_d(π̄') (mod d)`.
    `N(π') = π'·π̄'` as Eisenstein integers (`mul_conj_self`), so this is `char_mul` at `π'·π̄'`.
    ∅-axiom (PURE). -/
theorem eisChar_norm_split {d : ZOmega} (π' : ZOmega) {pr m : Nat}
    (hπ'norm : π'.normSq = (pr : Int)) :
    ModEq d (pow (ofInt ((pr : Nat) : Int)) m) (pow π' m * pow (conj π') m) := by
  have h1 : ofInt ((pr : Nat) : Int) = π' * conj π' := by rw [mul_conj_self π', hπ'norm]
  rw [h1]
  exact char_mul π' (conj π') m

/-- `(↑a)^m = ↑(a^m)` over `ℤ` — `Nat.cast` commutes with `^` (induction; `Int.natCast_pow`). -/
private theorem natcast_pow (a m : Nat) : ((a : Int)) ^ m = ((a ^ m : Nat) : Int) := by
  induction m with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ]; rw [show ((a ^ n * a : Nat) : Int)
      = ((a ^ n : Nat) : Int) * ((a : Nat) : Int) from rfl, ← ih]; rfl

/-- ★★★★ **The `𝔽_p` cubic character is the ℤ[ω] character of the embedded integer** —
    `χ_ω(t) ≡ χ_d(ofInt t) = (ofInt t)^m (mod d)` for a unit `0 < t < p`.  `chiOmega_lift`
    (`χ_ω(t) ≡ ofInt(t^m mod p)`) + `ofInt_natMod_modEq` (`ofInt(t^m mod p) ≡ ofInt(t^m)`) +
    `ofInt_pow` (`ofInt(t^m) = (ofInt t)^m`).  Bridges the rational `𝔽_p`-character `chiOmega` to the
    Eisenstein character `χ_d`.  ∅-axiom (PURE). -/
theorem chiOmega_eq_eisChar {d : ZOmega} {p m x t : Nat} (hp : 1 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d ZOmega.ZOmega.Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (ht1 : 0 < t) (htlt : t < p) :
    ModEq d (chiOmega p m x t) (pow (ofInt ((t : Nat) : Int)) m) := by
  have hlift := chiOmega_lift hp hpr h3m hdn hω hx ht1 htlt
  have hmod := ofInt_natMod_modEq (d := d) (p := p) (a := t ^ m) hdn
  have hpoweq : pow (ofInt ((t : Nat) : Int)) m = ofInt ((t ^ m : Nat) : Int) := by
    rw [ofInt_pow]; rw [natcast_pow t m]
  rw [hpoweq]
  exact trans (symm hlift) hmod

/-- ★★★★★ **The rational character of `N(π')` is the product of Eisenstein residue symbols** —

      `χ_ω(N(π')) ≡ χ_d(π') · χ_d(π̄')   (mod d)`        (`χ_d(π') = (π'/π)₃`).

    `chiOmega_eq_eisChar` (rational `χ_ω = χ_d` on the integer `N(π')`) + `eisChar_norm_split`
    (`χ_d(N(π')) = χ_d(π')·χ_d(π̄')`).  This is the mod-`d` half of cubic reciprocity: it ties the rational
    cubic character of the norm — the `χ̄(pr)` appearing in `split_conj_residue_relation` — to the
    Eisenstein residue symbols of `π'` and its conjugate at `π`.  ∅-axiom (PURE). -/
theorem chiOmega_norm_eq_symbol_product {d : ZOmega} {p m x pr : Nat} {π' : ZOmega} (hp : 1 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d ZOmega.ZOmega.Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hpr1 : 0 < pr) (hprlt : pr < p) (hπ'norm : π'.normSq = (pr : Int)) :
    ModEq d (chiOmega p m x pr) (pow π' m * pow (conj π') m) :=
  trans (chiOmega_eq_eisChar hp hpr h3m hdn hω hx hpr1 hprlt) (eisChar_norm_split π' hπ'norm)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharNormSplit
