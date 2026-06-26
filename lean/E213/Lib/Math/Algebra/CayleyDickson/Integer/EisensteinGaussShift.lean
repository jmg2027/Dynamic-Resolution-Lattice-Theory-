import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag

/-!
# The off-diagonal coefficient as a one-sided shifted sum (∅-axiom)

The `k≠0` convolution coefficient `(g⋆ḡ)(k) = Σ_{i<p} χ_ω(i)·conj χ_ω((i+p−k)%p)`
(`EisensteinGaussOffDiag.gauss_offdiag_sum`) is reindexed `i ↦ (j+k)%p` (the additive-shift
permutation `EisensteinRangeSum.rangeList_add_lperm`) to the cleaner one-sided form

  `(g⋆ḡ)(k) = Σ_{j<p} χ_ω((j+k)%p)·conj χ_ω(j)`   (`gauss_offdiag_shift`).

The inner index collapses to `j` itself (`add_shift_index`: `((j+k)%p + p − k)%p = j`), since
`(j+k) + (p−k) = j + p ≡ j`.  This is the form on which the `j⁻¹`-inversion + `k·`-multiplication
reindexes act to give the off-diagonal constant `−1` (the `e_k`-coefficient of `g·ḡ = p·1 − N`).
∅-axiom.  (A3 route b.)
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag (gauss_offdiag_sum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sum_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_lperm listSum_map)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
  (sumRange_eq_listSum rangeList_add_lperm add_p_mod)
open E213.Meta.Nat.AddMod213 (mod_add_mod)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel)
open E213.Tactic.NatHelper (add_sub_assoc)

/-- ★★★ **The additive-shift index** — `((j+k)%p + p − k) % p = j` for `j < p`, `k ≤ p`:
    `(j+k) + (p−k) = j + p ≡ j`.  Pure `ℕ` mod/sub arithmetic.  ∅-axiom. -/
theorem add_shift_index {p j k : Nat} (hp : 0 < p) (hk : k ≤ p) (hj : j < p) :
    ((j + k) % p + p - k) % p = j := by
  rw [add_sub_assoc ((j + k) % p) hk, mod_add_mod hp (j + k) (p - k),
      show j + k + (p - k) = j + p from by
        rw [Nat.add_assoc, Nat.add_comm k (p - k), nat_sub_add_cancel hk],
      add_p_mod hp, Nat.mod_eq_of_lt hj]

/-- ★★★★ **The off-diagonal coefficient as a one-sided shifted sum** — for `0 < k`, `k < p`,
    `(g⋆ḡ)(k) = Σ_{j<p} χ_ω((j+k)%p)·conj χ_ω(j)`.  Reindex the `gauss_offdiag_sum` form
    `i = (j+k)%p` (additive-shift permutation), with the inner index collapsing via
    `add_shift_index`.  The form the `j⁻¹`-inversion + `k·`-multiplication reindexes turn into `−1`.
    ∅-axiom. -/
theorem gauss_offdiag_shift {p m x k : Nat} (hk0 : 0 < k) (hk : k < p) :
    conv p (gauss p m x) (gaussConj p m x) k
      = sumRange (fun j => chiOmega p m x ((j + k) % p) * conj (chiOmega p m x j)) p := by
  have hp : 0 < p := Nat.lt_of_lt_of_le hk0 (Nat.le_of_lt hk)
  -- F i = χ_ω(i)·conj χ_ω((i+p−k)%p) ; reindex i = (j+k)%p over [0,p)
  rw [gauss_offdiag_sum hk,
      sumRange_eq_listSum _ p,
      listSum_lperm _ (rangeList_add_lperm hp (Nat.le_of_lt hk)),
      listSum_map _ (fun j => (j + k) % p),
      ← sumRange_eq_listSum _ p]
  refine sum_congr p (fun j hj => ?_)
  show chiOmega p m x ((j + k) % p) * conj (chiOmega p m x (((j + k) % p + p - k) % p))
     = chiOmega p m x ((j + k) % p) * conj (chiOmega p m x j)
  rw [add_shift_index hp (Nat.le_of_lt hk) hj]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift
