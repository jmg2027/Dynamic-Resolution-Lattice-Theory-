import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiIndex
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum

/-!
# The Gauss–Jacobi per-term identity — `χ((nt)/1)·χ(n−nt) = χ(n)²·χ(t)·χ(1−t)` (∅-axiom, A3 / route b)

The summand of `(g⋆g)(n) = Σ_i χ_ω(i)·χ_ω((n+p−i)%p)` under the multiplicative reindex `i = (n·t)%p`,
for a unit `t`:

  `χ_ω((n·t)%p) · χ_ω((n+p−(n·t)%p)%p) = χ_ω(n)²·(χ_ω(t)·χ_ω((1+(p−t))%p))`   (`gj_term`),

i.e. `χ(nt)·χ(n(1−t)) = χ(n)²·χ(t)·χ(1−t)`.  The index collapses by `gj_index`; each character factors
by `chiOmega_mul` (`χ(n)²` pulls out), leaving the Jacobi-sum summand `χ(t)·χ((1+(p−t))%p)`.  The wrap
`t=1` (`(1−t)≡0`) is handled (both sides `0`).  Summed over the units this gives `(g⋆g)(n)=χ(n)²·J`.
∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiTerm

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega mul_comm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiIndex (gj_index not_dvd_of_pos_lt)
open E213.Meta.Nat.AddMod213 (zero_mod)
open E213.Meta.Algebra213.Ring213 (mul_zero mul_assoc)

/-- **Middle-swap** — `(a·b)·(c·e) = (a·c)·(b·e)` in the commutative ring `ℤ[ω]`. -/
theorem mul_swap_mid (a b c e : ZOmega) : (a * b) * (c * e) = (a * c) * (b * e) := by
  rw [mul_assoc, ← mul_assoc b c e, mul_comm b c, mul_assoc c b e, ← mul_assoc a c (b * e)]

/-- ★★★★ **The Gauss–Jacobi per-term identity** — for `1 ≤ n, t < p` (`p ∤ n`),
    `χ_ω((n·t)%p)·χ_ω((n+p−(n·t)%p)%p) = χ_ω(n)²·(χ_ω(t)·χ_ω((1+(p−t))%p))`.  ∅-axiom. -/
theorem gj_term {d : ZOmega} {p m x n t : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hn1 : 1 ≤ n) (hnp : n < p) (ht1 : 1 ≤ t) (htp : t < p) :
    chiOmega p m x ((n * t) % p) * chiOmega p m x ((n + p - (n * t) % p) % p)
      = (chiOmega p m x n * chiOmega p m x n)
        * (chiOmega p m x t * chiOmega p m x ((1 + (p - t)) % p)) := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hnpn : ¬ p ∣ n := not_dvd_of_pos_lt hn1 hnp
  rw [gj_index hp hpr hnpn ht1 htp,
      ← chiOmega_mul hp hp3 hpr h3m hdn hω hx hn1 hnp ht1 htp]
  by_cases hwz : (1 + (p - t)) % p = 0
  · rw [hwz, Nat.mul_zero, zero_mod p,
        chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, mul_zero, mul_zero, mul_zero]
  · have hw1 : 0 < (1 + (p - t)) % p := Nat.pos_of_ne_zero hwz
    have hwp : (1 + (p - t)) % p < p := Nat.mod_lt _ hppos
    rw [← chiOmega_mul hp hp3 hpr h3m hdn hω hx hn1 hnp hw1 hwp]
    exact mul_swap_mid _ _ _ _

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiTerm
