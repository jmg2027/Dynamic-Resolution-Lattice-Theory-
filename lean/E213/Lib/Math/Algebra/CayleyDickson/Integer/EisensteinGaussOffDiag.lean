import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum

/-!
# The cubic Gauss sum's off-diagonal index helper (∅-axiom, Phase A3 / route b)

The `k≠0` convolution coefficient `(g⋆ḡ)(k) = Σ_{i<p} χ_ω(i)·conj χ_ω((p−(k+p−i)%p)%p)` has its inner
index simplified by

  `(p − (k+p−i) % p) % p = (i + p − k) % p`   (`conv_offdiag_index`),

i.e. the `(i−k) mod p` shift.  Pure `ℕ` mod/sub arithmetic (`add_sub_assoc`, `add_sub_add_right`,
`add_p_mod`, `sub_sub_self_pure`), case-split on `i ⋚ k`.  First brick of the off-diagonal coefficient
`(g⋆ḡ)(k) = −1` (A3 route b).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (add_p_mod sub_sub_self_pure)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sum_congr)
open E213.Meta.Nat.AddMod213 (mod_self)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel nat_add_sub_self_right)
open E213.Tactic.NatHelper (add_sub_assoc add_sub_add_right)

/-- Pure `i < k ⟹ 0 < k − i` (`Nat.sub_pos_of_lt` is `propext`-dirty). -/
private theorem sub_pos_pure {i k : Nat} (h : i < k) : 0 < k - i := by
  have h2 : (i + 1) - i ≤ k - i := Nat.sub_le_sub_right (Nat.succ_le_of_lt h) i
  rwa [Nat.add_comm i 1, nat_add_sub_self_right] at h2

/-- `i ≤ k ⟹ k + p − i = (k − i) + p`. -/
private theorem kpi_le {k i p : Nat} (h : i ≤ k) : k + p - i = (k - i) + p := by
  rw [Nat.add_comm k p, add_sub_assoc p h, Nat.add_comm p (k - i)]

/-- `i ≤ k ⟹ i + p − k = p − (k − i)`. -/
private theorem ipk_le {k i p : Nat} (h : i ≤ k) : i + p - k = p - (k - i) := by
  rw [Nat.add_comm i p, ← add_sub_add_right p i (k - i), nat_sub_add_cancel h]

/-- `k ≤ i ⟹ k + p − i = p − (i − k)`. -/
private theorem kpi_gt {k i p : Nat} (h : k ≤ i) : k + p - i = p - (i - k) := by
  rw [Nat.add_comm k p, ← add_sub_add_right p k (i - k), nat_sub_add_cancel h]

/-- `k ≤ i ⟹ i + p − k = (i − k) + p`. -/
private theorem ipk_gt {k i p : Nat} (h : k ≤ i) : i + p - k = (i - k) + p := by
  rw [Nat.add_comm i p, add_sub_assoc p h, Nat.add_comm p (i - k)]

/-- ★★★ **The off-diagonal index** — `(p − (k+p−i)%p)%p = (i+p−k)%p` for `i, k < p`: the `(i−k) mod p`
    shift the `k≠0` convolution coefficient reduces to.  Case-split `i ⋚ k`.  ∅-axiom. -/
theorem conv_offdiag_index {p k i : Nat} (hk : k < p) (hi : i < p) :
    (p - (k + p - i) % p) % p = (i + p - k) % p := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  rcases Nat.lt_trichotomy i k with hlt | heq | hgt
  · -- i < k
    have hik : i ≤ k := Nat.le_of_lt hlt
    have hkmi_lt : k - i < p := Nat.lt_of_le_of_lt (Nat.sub_le k i) hk
    rw [kpi_le hik, add_p_mod hp, Nat.mod_eq_of_lt hkmi_lt, ipk_le hik,
        Nat.mod_eq_of_lt (Nat.sub_lt hp (sub_pos_pure hlt))]
  · -- i = k
    subst heq
    rw [Nat.add_comm i p, nat_add_sub_self_right, mod_self, Nat.sub_zero, mod_self]
  · -- i > k
    have hki : k ≤ i := Nat.le_of_lt hgt
    have himk_lt : i - k < p := Nat.lt_of_le_of_lt (Nat.sub_le i k) hi
    rw [kpi_gt hki, Nat.mod_eq_of_lt (Nat.sub_lt hp (sub_pos_pure hgt)),
        sub_sub_self_pure (Nat.le_of_lt himk_lt), Nat.mod_eq_of_lt himk_lt,
        ipk_gt hki, add_p_mod hp, Nat.mod_eq_of_lt himk_lt]

/-- ★★★ **The off-diagonal convolution term** — for `i < p`, `gauss(i)·gaussConj((k+p−i)%p) =
    χ_ω(i)·conj χ_ω((i+p−k)%p)`.  `conv_offdiag_index` simplifies the index.  ∅-axiom. -/
theorem gauss_offdiag_term {p m x k i : Nat} (hk : k < p) (hi : i < p) :
    gauss p m x i * gaussConj p m x ((k + p - i) % p)
      = chiOmega p m x i * conj (chiOmega p m x ((i + p - k) % p)) := by
  show chiOmega p m x i * conj (chiOmega p m x ((p - (k + p - i) % p) % p))
     = chiOmega p m x i * conj (chiOmega p m x ((i + p - k) % p))
  rw [conv_offdiag_index hk hi]

/-- ★★★★ **The off-diagonal coefficient as a shifted character sum** — for `k < p`,
    `(g⋆ḡ)(k) = Σ_{i<p} χ_ω(i)·conj χ_ω((i+p−k)%p)`.  `gauss_offdiag_term` under `sum_congr`.  The form
    the multiplicative reindex `i=(k·u)%p` collapses to the `k`-independent constant `C = −1`.  ∅-axiom. -/
theorem gauss_offdiag_sum {p m x k : Nat} (hk : k < p) :
    conv p (gauss p m x) (gaussConj p m x) k
      = sumRange (fun i => chiOmega p m x i * conj (chiOmega p m x ((i + p - k) % p))) p := by
  show sumRange (fun i => gauss p m x i * gaussConj p m x ((k + p - i) % p)) p = _
  exact sum_congr p (fun i hi => gauss_offdiag_term hk hi)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag
