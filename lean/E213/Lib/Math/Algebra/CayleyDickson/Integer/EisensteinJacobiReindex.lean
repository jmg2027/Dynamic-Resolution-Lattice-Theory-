import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel

/-!
# The Jacobi-sum reindex identity — `χ_ω(b·c)·χ̄_ω(b) = χ_ω(c)` (∅-axiom, Phase A3 step 4)

The per-term simplification driving the `N(J) = p` reindexing.  For units `b, c`,

  `χ_ω((b·c) mod p) · conj χ_ω(b) = χ_ω(c)`.

`χ_ω((b·c)%p) = χ_ω(b)·χ_ω(c)` (`chiOmega_mul`), and `χ_ω(b)·conj χ_ω(b) = 1` (`chiOmega_mul_conj`,
unit norm), so the `χ_ω(b)` factors cancel.  Under the substitution `a = (b·c) mod p` this turns the
Jacobi double-sum term `χ_ω(a)·χ̄_ω(b)` into `χ_ω(c)` — the form on which the inner character sum
collapses by orthogonality `Σ_c χ_ω(c) = 0` (A3 step 4).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
  (chiOmega chiOmega_unit_value chiOmega_mul_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (one_mul_zomega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Meta.Algebra213.Ring213 (mul_assoc)

/-- ★★ **A unit's character value is nonzero** — `χ_ω(b) ≠ 0` for `0 < b < p` (it is in `{1,ω,ω²}`). -/
theorem chiOmega_ne_zero (p m x b : Nat) (hb1 : 0 < b) (hblt : b < p) :
    chiOmega p m x b ≠ 0 := by
  rcases chiOmega_unit_value p m x b hb1 hblt with h | h | h <;> rw [h] <;> decide

/-- ★★★★ **The Jacobi reindex identity** — `χ_ω((b·c) mod p) · conj χ_ω(b) = χ_ω(c)` for units `b, c`.
    `χ_ω(b·c) = χ_ω(b)·χ_ω(c)` (`chiOmega_mul`); the `χ_ω(b)·conj χ_ω(b) = 1` factors cancel
    (`chiOmega_mul_conj`).  The substitution `a = b·c` rewriting of the norm double-sum term.  ∅-axiom. -/
theorem chiOmega_reindex {d : ZOmega} {p m x b c : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hb1 : 0 < b) (hblt : b < p) (hc1 : 0 < c) (hclt : c < p) :
    chiOmega p m x ((b * c) % p) * conj (chiOmega p m x b) = chiOmega p m x c := by
  rw [← chiOmega_mul hp hp3 hpr h3m hdn hω hx hb1 hblt hc1 hclt]
  have hunit := chiOmega_mul_conj p m x b (chiOmega_ne_zero p m x b hb1 hblt)
  calc chiOmega p m x b * chiOmega p m x c * conj (chiOmega p m x b)
      = chiOmega p m x b * conj (chiOmega p m x b) * chiOmega p m x c := by
        rw [mul_assoc, ZOmega.mul_comm (chiOmega p m x c) (conj (chiOmega p m x b)), ← mul_assoc]
    _ = ofInt 1 * chiOmega p m x c := by rw [hunit]
    _ = chiOmega p m x c := one_mul_zomega _

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex
