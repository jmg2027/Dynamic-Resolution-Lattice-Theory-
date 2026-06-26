import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
import E213.Lib.Math.Combinatorics.RangeList
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor

/-!
# Splitting a `[0,p)` sum into its `0`-term and the unit sum (∅-axiom)

For a prime `p`, the full residue list `rangeList p = [0,p)` is `0 :: totativeList p` up to permutation
(every nonzero residue below a prime is a unit).  Hence a `ℤ[ω]`-valued sum over `[0,p)` splits:

  `listSum F (rangeList p) = F 0 + listSum F (totativeList p)`   (`listSum_rangeList_split`).

This is the bridge from the additive-shift form `(g⋆ḡ)(k) = Σ_{j<p} χ_ω((j+k)%p)·χ̄_ω(j)`
(`EisensteinGaussShift`) — a sum over `[0,p)` — to the **units sum** the `j⁻¹`-inversion permutation
(`EisensteinInvPerm.totativeList_inv_lperm`) acts on, dropping the `j=0` term (where `χ̄_ω(0)=0`).
Membership `mem_totativeList_prime`: for prime `p`, `x ∈ totativeList p ↔ 1 ≤ x ∧ x < p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeTotatives

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_lperm)
open E213.Lib.Math.Combinatorics.RangeList (rangeList mem_rangeList nodup_rangeList)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_pos totativeList_le totativeList_coprime totative_lt_n
   nodup_totativeList mem_totListUpto lperm_of_nodup_mem_iff)
open E213.Lib.Math.Combinatorics.Permutations (LPerm)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213 (gcd213_comm)

/-- ★★ **Totative membership for a prime** — `x ∈ totativeList p ↔ 1 ≤ x ∧ x < p` (`1 < p`, `p` prime):
    every residue `1 ≤ x < p` is coprime to a prime.  ∅-axiom. -/
theorem mem_totativeList_prime {p x : Nat} (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    x ∈ totativeList p ↔ (1 ≤ x ∧ x < p) := by
  constructor
  · intro h
    exact ⟨totativeList_pos h,
      totative_lt_n hp (totativeList_coprime h) (totativeList_pos h) (totativeList_le h)⟩
  · intro ⟨h1, h2⟩
    have hnd : ¬ p ∣ x := by
      intro ⟨c, hc⟩
      cases c with
      | zero => rw [Nat.mul_zero] at hc; exact absurd (hc ▸ h1) (by decide)
      | succ c' =>
          have hpx : p ≤ x := by rw [hc, Nat.mul_succ]; exact Nat.le_add_left p (p * c')
          exact absurd h2 (Nat.not_lt.mpr hpx)
    have hco : gcd213 x p = 1 := by rw [gcd213_comm]; exact prime_coprime p x hpr hnd
    exact mem_totListUpto.mpr ⟨h1, Nat.le_of_lt h2, hco⟩

/-- **`rangeList p` permutes `0 :: totativeList p`** for a prime `p`: the residues `[0,p)` are `0`
    together with the units `[1,p)`.  ∅-axiom. -/
theorem rangeList_perm_cons_totatives {p : Nat} (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) : LPerm (rangeList p) (0 :: totativeList p) := by
  have hp0 : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le 1) hp
  refine lperm_of_nodup_mem_iff (nodup_rangeList p) ?_ (fun x => ?_)
  · refine List.Pairwise.cons ?_ (nodup_totativeList p)
    intro y hy heq
    subst heq
    exact absurd (totativeList_pos hy) (by decide)
  · constructor
    · intro hx
      have hxp : x < p := mem_rangeList.mp hx
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · rw [h0]; exact List.Mem.head _
      · exact List.Mem.tail _ ((mem_totativeList_prime hp hpr).mpr ⟨hpos, hxp⟩)
    · intro hx
      cases hx with
      | head => exact mem_rangeList.mpr hp0
      | tail _ h' => exact mem_rangeList.mpr ((mem_totativeList_prime hp hpr).mp h').2

/-- ★★★★ **The `[0,p)` sum splits off its `0`-term** — `listSum F (rangeList p) = F 0 +
    listSum F (totativeList p)` for a prime `p`.  Permute `rangeList p` to `0 :: totativeList p`
    (`rangeList_perm_cons_totatives`) and split the head (`listSum_cons`).  The bridge from the
    `[0,p)` Gauss-sum coefficient to the units sum the inversion reindex needs.  ∅-axiom. -/
theorem listSum_rangeList_split (F : Nat → ZOmega) {p : Nat} (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    listSum F (rangeList p) = F 0 + listSum F (totativeList p) := by
  rw [listSum_lperm F (rangeList_perm_cons_totatives hp hpr)]
  rfl

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeTotatives
