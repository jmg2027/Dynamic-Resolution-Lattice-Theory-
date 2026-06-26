import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
import E213.Lib.Math.Combinatorics.RangeList
import E213.Lib.Math.NumberTheory.EulerTheorem

/-!
# Bridging `sumRange [0,n)` to `listSum (rangeList n)` (∅-axiom, Phase A3 / route b)

`EisensteinFiniteSum.sumRange f n` (the indexed sum over `[0,n)`) equals `listSum f (rangeList n)` (the
list sum over the pure range list) — `sumRange_eq_listSum`.  This lets the convolution sums of the Gauss
sum (defined via `sumRange`) be **reindexed by permutations of `[0,p)`** (`listSum_lperm` over
`rangeList`), the mechanism the off-diagonal coefficient `(g⋆ḡ)(k) = −1` needs (`research-notes/
frontiers/higher_reciprocity_roadmap.md`, A3 route b).  Same terms, order swapped — `add_comm`.

Also `rangeList_mul_lperm`: for a unit `a` (`gcd(a,p)=1`), `i ↦ (a·i) mod p` permutes **all** of
`[0,p)` (the full-range analogue of `EulerTheorem.lperm_image`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_cons)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sumRange_succ)
open E213.Lib.Math.Combinatorics.RangeList (rangeList mem_rangeList nodup_rangeList)
open E213.Lib.Math.Combinatorics.Permutations (LPerm)
open E213.Lib.Math.NumberTheory.EulerTheorem (aInv inv_mul_image mul_inv_image lperm_of_nodup_mem_iff)
open E213.Tactic.List213 (nodup_map_of_inj mem_map_of_mem exists_of_mem_map)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Algebra213.Ring213 (add_comm)

/-- ★★★ **`sumRange = listSum ∘ rangeList`** — the indexed sum over `[0,n)` is the list sum over
    `rangeList n`.  Induction + `add_comm` (the lists are reverse-ordered).  ∅-axiom. -/
theorem sumRange_eq_listSum (f : Nat → ZOmega) : ∀ n, sumRange f n = listSum f (rangeList n)
  | 0 => rfl
  | n + 1 => by
      rw [sumRange_succ, sumRange_eq_listSum f n]
      show listSum f (rangeList n) + f n = listSum f (n :: rangeList n)
      rw [listSum_cons, add_comm]

/-- ★★★★ **The full-range multiplicative permutation** — for a unit `a` (`gcd(a,p)=1`),
    `i ↦ (a·i) mod p` permutes **all** of `[0,p)`: `LPerm (rangeList p) (map (a··) (rangeList p))`.  The
    full-range analogue of `EulerTheorem.lperm_image`: injective by the modular inverse `aInv`
    (`inv_mul_image`), surjective by `mul_inv_image`.  ∅-axiom. -/
theorem rangeList_mul_lperm {p a : Nat} (hp : 0 < p) (ha : gcd213 a p = 1) :
    LPerm (rangeList p) ((rangeList p).map (fun i => (a * i) % p)) := by
  have hinj : ∀ i, i ∈ rangeList p → ∀ j, j ∈ rangeList p → (a * i) % p = (a * j) % p → i = j := by
    intro i hi j hj he
    have h1 : (aInv a p * ((a * i) % p)) % p = (aInv a p * ((a * j) % p)) % p := by rw [he]
    rw [inv_mul_image hp ha, inv_mul_image hp ha,
        Nat.mod_eq_of_lt (mem_rangeList.mp hi), Nat.mod_eq_of_lt (mem_rangeList.mp hj)] at h1
    exact h1
  refine lperm_of_nodup_mem_iff (nodup_rangeList p)
    (nodup_map_of_inj hinj (nodup_rangeList p)) (fun y => ?_)
  constructor
  · intro hy
    have himg : (a * ((aInv a p * y) % p)) % p = y := by
      rw [mul_inv_image hp ha, Nat.mod_eq_of_lt (mem_rangeList.mp hy)]
    rw [← himg]
    exact mem_map_of_mem (fun i => (a * i) % p) (mem_rangeList.mpr (Nat.mod_lt _ hp))
  · intro hy
    obtain ⟨i, _, rfl⟩ := exists_of_mem_map hy
    exact mem_rangeList.mpr (Nat.mod_lt _ hp)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
