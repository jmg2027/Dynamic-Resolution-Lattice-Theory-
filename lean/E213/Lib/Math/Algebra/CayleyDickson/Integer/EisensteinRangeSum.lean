import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
import E213.Lib.Math.Combinatorics.RangeList
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatRing213

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
open E213.Meta.Nat.AddMod213 (add_mod add_mod_left mod_self mod_mod)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel nat_add_sub_self_right)

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

/-- Pure `(a + p) % p = a % p`. -/
theorem add_p_mod {p : Nat} (hp : 0 < p) (a : Nat) : (a + p) % p = a % p := by
  rw [add_mod hp a p, mod_self, Nat.add_zero, mod_mod]

/-- Pure `p − (p − c) = c` for `c ≤ p`. -/
theorem sub_sub_self_pure {c p : Nat} (h : c ≤ p) : p - (p - c) = c := by
  have key : c + (p - c) = p := by rw [Nat.add_comm]; exact nat_sub_add_cancel h
  calc p - (p - c) = (c + (p - c)) - (p - c) := by rw [key]
    _ = c := nat_add_sub_self_right c (p - c)

/-- The additive-shift inverse cancels: `((i + c) % p + (p − c)) % p = i` for `i < p`, `c ≤ p`. -/
private theorem add_shift_cancel {p c : Nat} (hp : 0 < p) (hc : c ≤ p) {i : Nat} (hi : i < p) :
    ((i + c) % p + (p - c)) % p = i := by
  rw [← add_mod_left hp (i + c) (p - c),
      show i + c + (p - c) = i + p from by
        rw [Nat.add_assoc, Nat.add_comm c (p - c), nat_sub_add_cancel hc],
      add_p_mod hp, Nat.mod_eq_of_lt hi]

/-- ★★★★ **The full-range additive-shift permutation** — `i ↦ (i + c) mod p` permutes `[0,p)` for
    `c ≤ p`: `LPerm (rangeList p) (map (·+c) (rangeList p))`.  Injective/surjective by the shift inverse
    `· + (p−c)` (`add_shift_cancel`).  The additive sibling of `rangeList_mul_lperm`, for the Gauss-sum
    off-diagonal's `u ↦ u−1` reindex.  ∅-axiom. -/
theorem rangeList_add_lperm {p c : Nat} (hp : 0 < p) (hc : c ≤ p) :
    LPerm (rangeList p) ((rangeList p).map (fun i => (i + c) % p)) := by
  have hinj : ∀ i, i ∈ rangeList p → ∀ j, j ∈ rangeList p → (i + c) % p = (j + c) % p → i = j := by
    intro i hi j hj he
    have ei := add_shift_cancel hp hc (mem_rangeList.mp hi)
    have ej := add_shift_cancel hp hc (mem_rangeList.mp hj)
    rw [← ei, ← ej, he]
  refine lperm_of_nodup_mem_iff (nodup_rangeList p)
    (nodup_map_of_inj hinj (nodup_rangeList p)) (fun y => ?_)
  constructor
  · intro hy
    have himg : ((y + (p - c)) % p + c) % p = y := by
      have h := add_shift_cancel hp (Nat.sub_le p c) (i := y) (mem_rangeList.mp hy)
      rwa [sub_sub_self_pure hc] at h
    rw [← himg]
    exact mem_map_of_mem (fun i => (i + c) % p) (mem_rangeList.mpr (Nat.mod_lt _ hp))
  · intro hy
    obtain ⟨i, _, rfl⟩ := exists_of_mem_map hy
    exact mem_rangeList.mpr (Nat.mod_lt _ hp)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
