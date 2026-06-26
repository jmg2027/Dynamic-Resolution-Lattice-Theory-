import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum

/-!
# Convolution is commutative — `f ⋆ g = g ⋆ f` (∅-axiom)

In the group ring `R[C_p]`, convolution is commutative (coefficientwise, for `k < p`):

  `(f ⋆ g)(k) = (g ⋆ f)(k)`   (`conv_comm`).

Reindex by the **reflection** `i ↦ (k+p−i)%p` (an involution `refl_invol`, hence a permutation of
`[0,p)` — `rangeList_refl_lperm`); the summand `f(i)·g((k−i)) ↦ f((k−i))·g(i)`, equal to `g(i)·f((k−i))`
by `mul_comm`.  Commutativity (with associativity) lets `(g·ḡ)² = (g·g)·(ḡ·ḡ)`, the reassociation
behind `N(J)=p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (mul_comm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
  (listSum listSum_congr listSum_map listSum_lperm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
  (sumRange_eq_listSum add_p_mod sub_sub_self_pure)
open E213.Lib.Math.Combinatorics.RangeList (rangeList mem_rangeList nodup_rangeList)
open E213.Lib.Math.Combinatorics.Permutations (LPerm)
open E213.Lib.Math.NumberTheory.EulerTheorem (lperm_of_nodup_mem_iff)
open E213.Tactic.List213 (nodup_map_of_inj mem_map_of_mem exists_of_mem_map)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel)
open E213.Tactic.NatHelper (add_sub_assoc add_sub_add_right)

/-- `i < k ⟹ 0 < k − i` (pure; `Nat.sub_pos_of_lt` leaks propext). -/
private theorem sub_pos_pure {i k : Nat} (h : i < k) : 0 < k - i := by
  have h2 : (i + 1) - i ≤ k - i := Nat.sub_le_sub_right (Nat.succ_le_of_lt h) i
  rwa [Nat.add_comm i 1, E213.Meta.Nat.NatRing213.nat_add_sub_self_right] at h2

/-- ★★★ **The reflection is an involution** — `(k+p − (k+p−i)%p) % p = i` for `i < p`, `k < p`.
    Case-split `i ≤ k` vs `k < i`.  ∅-axiom. -/
theorem refl_invol {p k i : Nat} (hp : 0 < p) (hk : k < p) (hi : i < p) :
    (k + p - (k + p - i) % p) % p = i := by
  rcases Nat.lt_or_ge k i with hgt | hik
  · -- k < i : (k+p−i)%p = p−(i−k), then (k+p−(p−(i−k)))%p = (k+(i−k))%p = i
    have hki : k ≤ i := Nat.le_of_lt hgt
    have he2 : k + p - i = p - (i - k) := by
      rw [Nat.add_comm k p, ← add_sub_add_right p k (i - k), nat_sub_add_cancel hki]
    have hpik_lt : p - (i - k) < p := Nat.sub_lt hp (sub_pos_pure hgt)
    have himk_le : i - k ≤ p := Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le i k) hi)
    rw [he2, Nat.mod_eq_of_lt hpik_lt, add_sub_assoc k (Nat.sub_le p (i - k)),
        sub_sub_self_pure himk_le,
        show k + (i - k) = i from by rw [Nat.add_comm k (i - k), nat_sub_add_cancel hki],
        Nat.mod_eq_of_lt hi]
  · -- i ≤ k : (k+p−i)%p = k−i, then (k+p−(k−i))%p = (p+i)%p = i
    have he1 : k + p - i = (k - i) + p := by
      rw [Nat.add_comm k p, add_sub_assoc p hik, Nat.add_comm p (k - i)]
    have hkilt : k - i < p := Nat.lt_of_le_of_lt (Nat.sub_le k i) hk
    rw [he1, add_p_mod hp, Nat.mod_eq_of_lt hkilt, Nat.add_comm k p,
        add_sub_assoc p (Nat.sub_le k i), sub_sub_self_pure hik, Nat.add_comm p i,
        add_p_mod hp, Nat.mod_eq_of_lt hi]

/-- ★★★★ **The reflection permutes `[0,p)`** — `LPerm (rangeList p) (map (fun i => (k+p−i)%p) (rangeList p))`
    for `k < p`.  Injective/surjective by the involution `refl_invol`.  ∅-axiom. -/
theorem rangeList_refl_lperm {p k : Nat} (hp : 0 < p) (hk : k < p) :
    LPerm (rangeList p) ((rangeList p).map (fun i => (k + p - i) % p)) := by
  have hinj : ∀ i, i ∈ rangeList p → ∀ j, j ∈ rangeList p →
      (k + p - i) % p = (k + p - j) % p → i = j := by
    intro i hi j hj he
    have ei := refl_invol hp hk (mem_rangeList.mp hi)
    have ej := refl_invol hp hk (mem_rangeList.mp hj)
    rw [← ei, he, ej]
  refine lperm_of_nodup_mem_iff (nodup_rangeList p)
    (nodup_map_of_inj hinj (nodup_rangeList p)) (fun y => ?_)
  constructor
  · intro hy
    have hyp : y < p := mem_rangeList.mp hy
    rw [← refl_invol hp hk hyp]
    exact mem_map_of_mem (fun i => (k + p - i) % p) (mem_rangeList.mpr (Nat.mod_lt _ hp))
  · intro hy
    obtain ⟨i, _, rfl⟩ := exists_of_mem_map hy
    exact mem_rangeList.mpr (Nat.mod_lt _ hp)

/-- ★★★★★ **Convolution is commutative** — `(f ⋆ g)(k) = (g ⋆ f)(k)` for `k < p`.  Reflection reindex
    `i ↦ (k+p−i)%p` + `mul_comm`.  ∅-axiom. -/
theorem conv_comm (p : Nat) (f g : Nat → ZOmega) {k : Nat} (hk : k < p) :
    conv p f g k = conv p g f k := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  show sumRange (fun i => f i * g ((k + p - i) % p)) p
     = sumRange (fun i => g i * f ((k + p - i) % p)) p
  rw [sumRange_eq_listSum, sumRange_eq_listSum,
      listSum_lperm (fun i => f i * g ((k + p - i) % p)) (rangeList_refl_lperm hp hk),
      listSum_map (fun i => f i * g ((k + p - i) % p)) (fun i => (k + p - i) % p) (rangeList p)]
  refine listSum_congr (rangeList p) (fun i hi => ?_)
  show f ((k + p - i) % p) * g ((k + p - (k + p - i) % p) % p) = g i * f ((k + p - i) % p)
  rw [refl_invol hp hk (mem_rangeList.mp hi), mul_comm]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm
