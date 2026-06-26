import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiTerm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeTotatives
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum

/-!
# The Gauss–Jacobi relation `g(χ)² = J·g(χ²)` at unit coefficients (∅-axiom)

The `e_n`-coefficient (`0<n<p`) of `g(χ)²` in the group ring:

  `(g ⋆ g)(n) = jacobiSum · χ_ω(n)²`   (`gauss_sq_unit`),

i.e. `Σ_i χ_ω(i)·χ_ω((n−i)) = J·χ_ω(n)²`.  Drop `i=0` (`χ_ω(0)=0`), reindex `i=(n·t)%p`
(`lperm_image`), apply the per-term `gj_term` (`χ(nt)·χ(n(1−t)) = χ(n)²·χ(t)·χ(1−t)`), pull out
`χ(n)²` (`listSum_mul_left`); the remaining sum is the Jacobi sum (`jacobi_eq_listSum`).  This is the
Gauss–Jacobi relation `g(χ)² = J·g(χ²)` (`g(χ²)(n) = χ_ω(n)² = χ²(n)`) feeding `N(J)=p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobi

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega mul_comm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiTerm (gj_term)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
  (listSum listSum_congr listSum_map listSum_lperm listSum_mul_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (sumRange_eq_listSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeTotatives
  (mem_totativeList_prime listSum_rangeList_split)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_pos totativeList_le totativeList_coprime totative_lt_n lperm_image)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Algebra213.Ring213 (zero_mul zero_add)

/-- `jacobiSum = Σ_{t∈tot} χ_ω(t)·χ_ω((1+(p−t))%p)` — the Jacobi sum as a units list sum (the `t=0`
    term vanishes, `χ_ω(0)=0`).  ∅-axiom. -/
theorem jacobi_eq_listSum {p : Nat} (m x : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    jacobiSum p m x
      = listSum (fun t => chiOmega p m x t * chiOmega p m x ((1 + (p - t)) % p)) (totativeList p) := by
  show sumRange (fun t => chiOmega p m x t * chiOmega p m x ((1 + (p - t)) % p)) p = _
  rw [sumRange_eq_listSum, listSum_rangeList_split _ hp hpr,
      show chiOmega p m x 0 * chiOmega p m x ((1 + (p - 0)) % p) = 0 from by
        rw [chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, zero_mul], zero_add]

/-- ★★★★★ **The Gauss–Jacobi relation at a unit coefficient** — for `0<n<p`,
    `(g⋆g)(n) = jacobiSum · χ_ω(n)²`.  Reindex `i=(n·t)%p` + per-term `gj_term` + pull out `χ(n)²`.
    ∅-axiom. -/
theorem gauss_sq_unit {d : ZOmega} {p m x n : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hn1 : 1 ≤ n) (hnp : n < p) :
    conv p (gauss p m x) (gauss p m x) n
      = jacobiSum p m x * (chiOmega p m x n * chiOmega p m x n) := by
  have hnc : gcd213 n p = 1 :=
    totativeList_coprime ((mem_totativeList_prime hp hpr).mpr ⟨hn1, hnp⟩)
  show sumRange (fun i => chiOmega p m x i * chiOmega p m x ((n + p - i) % p)) p = _
  rw [sumRange_eq_listSum, listSum_rangeList_split _ hp hpr,
      show chiOmega p m x 0 * chiOmega p m x ((n + p - 0) % p) = 0 from by
        rw [chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, zero_mul], zero_add,
      listSum_lperm _ (lperm_image hp hnc),
      listSum_map (fun i => chiOmega p m x i * chiOmega p m x ((n + p - i) % p))
        (fun t => (n * t) % p) (totativeList p),
      listSum_congr (totativeList p) (fun t ht =>
        gj_term hp hp3 hpr h3m hdn hω hx hn1 hnp (totativeList_pos ht)
          (totative_lt_n hp (totativeList_coprime ht) (totativeList_pos ht) (totativeList_le ht))),
      listSum_mul_left (chiOmega p m x n * chiOmega p m x n)
        (fun t => chiOmega p m x t * chiOmega p m x ((1 + (p - t)) % p)) (totativeList p),
      ← jacobi_eq_listSum m x hp hpr, mul_comm]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobi
