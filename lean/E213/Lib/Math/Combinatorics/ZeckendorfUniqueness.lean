import E213.Lib.Math.Combinatorics.Zeckendorf
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.NatRing213

/-!
# Zeckendorf's theorem — uniqueness (∅-axiom)

The companion to `Zeckendorf` (existence): the non-consecutive Fibonacci
representation is **unique**.  Together they are the full Zeckendorf theorem.

  ★ **`zeckendorf_unique`**: two valid (`AllGe2` + `NonConsec`) index lists with
    the same Fibonacci sum are equal.

The mathematical heart:

  ★ **`sum_lt_fib_head_succ`** — a valid Zeckendorf sum with top index `i` is
    strictly below `fib (i+1)`.  ("Greedy is forced": `fib i` is the unique largest
    `fib · ≤ n`.)  The gap condition (`NonConsec`: next index `≤ i−2`) makes the
    tail sum `< fib(i−1)`, so total `< fib i + fib(i−1) = fib(i+1)`.

Uniqueness then follows: both lists' heads are the unique index bracketing the sum
(`head_brackets` + `heads_eq`, by trichotomy), so heads agree; peel `fib i` via
`nat_add_left_cancel` and recurse on tails.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.ZeckendorfUniqueness

open E213.Lib.Math.Combinatorics.Zeckendorf
open E213.Tactic.NatHelper (sub_add_cancel sub_one_add_one)

/-! ## Auxiliary fib facts -/

/-- For `i ≥ 2`: `fib i + fib (i-1) = fib (i+1)`.  (Reindex of `fib_rec`.) -/
theorem fib_head_telescope {i : Nat} (hi : 2 ≤ i) :
    fib i + fib (i - 1) = fib (i + 1) := by
  have h1 : 1 ≤ i := Nat.le_trans (by decide) hi
  have ine0 : i ≠ 0 := by intro h; rw [h] at h1; exact absurd h1 (by decide)
  have key : (i - 1) + 1 = i := sub_one_add_one ine0
  have e1 : i + 1 = (i - 1) + 2 := by
    rw [show (i - 1) + 2 = ((i - 1) + 1) + 1 from by ring_nat, key]
  rw [e1, show fib ((i - 1) + 2) = fib (i - 1) + fib ((i - 1) + 1) from fib_rec (i - 1), key]
  exact Nat.add_comm (fib i) (fib (i - 1))

/-- `fib i < fib (i+1)` strictly, for `i ≥ 2`. -/
theorem fib_lt_succ {i : Nat} (hi : 2 ≤ i) : fib i < fib (i + 1) := by
  have htel := fib_head_telescope hi
  have h1 : 1 ≤ i := Nat.le_trans (by decide) hi
  have ine0 : i ≠ 0 := by intro h; rw [h] at h1; exact absurd h1 (by decide)
  have key : (i - 1) + 1 = i := sub_one_add_one ine0
  have hi1 : 1 ≤ i - 1 := by
    rw [← key] at hi
    exact Nat.le_of_succ_le_succ hi
  have ine1 : i - 1 ≠ 0 := by intro h; rw [h] at hi1; exact absurd hi1 (by decide)
  have key2 : (i - 1 - 1) + 1 = i - 1 := sub_one_add_one ine1
  have hpos : 1 ≤ fib (i - 1) := by
    rw [← key2]; exact one_le_fib_succ (i - 1 - 1)
  have hlt : fib i < fib i + fib (i - 1) := Nat.lt_add_of_pos_right hpos
  rw [htel] at hlt
  exact hlt

/-! ## The crux: a Zeckendorf sum with top index `i` is `< fib (i+1)` -/

/-- ★ **Crux lemma.**  For a valid (`AllGe2` + `NonConsec`) list with head index `i`,
    the Fibonacci sum is strictly below `fib (i+1)`.  This is "greedy is forced": the
    top Fibonacci `fib i` is the unique largest `fib · ≤ n`. -/
theorem sum_lt_fib_head_succ :
    ∀ (i : Nat) (rest : List Nat),
      AllGe2 (i :: rest) → NonConsec (i :: rest) →
      sumFibIndices (i :: rest) < fib (i + 1)
  | i, [], hge2, _ => by
      have hi : 2 ≤ i := hge2.1
      rw [sumFibIndices_cons]
      show fib i + sumFibIndices [] < fib (i + 1)
      rw [show sumFibIndices ([] : List Nat) = 0 from rfl, Nat.add_zero]
      exact fib_lt_succ hi
  | i, j :: rest', hge2, hnc => by
      have hi : 2 ≤ i := hge2.1
      have hgap : j + 2 ≤ i := hnc.1
      have hnc' : NonConsec (j :: rest') := hnc.2
      have hge2' : AllGe2 (j :: rest') := hge2.2
      have ih : sumFibIndices (j :: rest') < fib (j + 1) :=
        sum_lt_fib_head_succ j rest' hge2' hnc'
      have hj1_le : j + 1 ≤ i - 1 := by
        have h2 : (j + 1) + 1 ≤ i := by
          rw [show (j + 1) + 1 = j + 2 from by ring_nat]; exact hgap
        exact E213.Tactic.NatHelper.le_sub_of_add_le h2
      have hfib_le : fib (j + 1) ≤ fib (i - 1) := fib_mono hj1_le
      rw [sumFibIndices_cons]
      have step : fib i + sumFibIndices (j :: rest') < fib i + fib (i - 1) :=
        Nat.add_lt_add_left (Nat.lt_of_lt_of_le ih hfib_le) (fib i)
      rw [fib_head_telescope hi] at step
      exact step

/-! ## Toward uniqueness -/

/-- A nonempty valid list has sum `≥ fib 2 = 1` (strictly positive). -/
theorem sum_pos_of_cons (i : Nat) (rest : List Nat)
    (hge2 : AllGe2 (i :: rest)) : 1 ≤ sumFibIndices (i :: rest) := by
  have hi : 2 ≤ i := hge2.1
  have hfib : 1 ≤ fib i := by
    have h := fib_mono hi
    rw [fib_two] at h; exact h
  rw [sumFibIndices_cons]
  exact Nat.le_trans hfib (Nat.le_add_right (fib i) (sumFibIndices rest))

/-- The head index brackets the sum: `fib i ≤ n < fib (i+1)`. -/
theorem head_brackets (i : Nat) (rest : List Nat)
    (hge2 : AllGe2 (i :: rest)) (hnc : NonConsec (i :: rest)) :
    fib i ≤ sumFibIndices (i :: rest) ∧ sumFibIndices (i :: rest) < fib (i + 1) :=
  ⟨head_fib_le_sum i rest, sum_lt_fib_head_succ i rest hge2 hnc⟩

/-- **Head agreement.**  Two valid nonempty lists with equal sum have equal head. -/
theorem heads_eq (i k : Nat) (r1 r2 : List Nat)
    (hge1 : AllGe2 (i :: r1)) (hnc1 : NonConsec (i :: r1))
    (hge2 : AllGe2 (k :: r2)) (hnc2 : NonConsec (k :: r2))
    (heq : sumFibIndices (i :: r1) = sumFibIndices (k :: r2)) : i = k := by
  obtain ⟨hlo1, hhi1⟩ := head_brackets i r1 hge1 hnc1
  obtain ⟨hlo2, hhi2⟩ := head_brackets k r2 hge2 hnc2
  rcases Nat.lt_trichotomy i k with hlt | heqik | hgt
  · have hik : i + 1 ≤ k := hlt
    have hfib_le : fib (i + 1) ≤ fib k := fib_mono hik
    have hk_le_sum1 : fib k ≤ sumFibIndices (i :: r1) := by
      rw [heq]; exact hlo2
    have : fib (i + 1) ≤ sumFibIndices (i :: r1) := Nat.le_trans hfib_le hk_le_sum1
    exact absurd (Nat.lt_of_le_of_lt this hhi1) (Nat.lt_irrefl _)
  · exact heqik
  · have hki : k + 1 ≤ i := hgt
    have hfib_le : fib (k + 1) ≤ fib i := fib_mono hki
    have hi_le_sum2 : fib i ≤ sumFibIndices (k :: r2) := by
      rw [← heq]; exact hlo1
    have : fib (k + 1) ≤ sumFibIndices (k :: r2) := Nat.le_trans hfib_le hi_le_sum2
    exact absurd (Nat.lt_of_le_of_lt this hhi2) (Nat.lt_irrefl _)

/-- ★★★ **Zeckendorf uniqueness.**  Two valid (`AllGe2` + `NonConsec`) lists that
    represent the same `n` are equal. -/
theorem zeckendorf_unique :
    ∀ (L1 L2 : List Nat),
      AllGe2 L1 → NonConsec L1 → AllGe2 L2 → NonConsec L2 →
      sumFibIndices L1 = sumFibIndices L2 → L1 = L2
  | [], [], _, _, _, _, _ => rfl
  | [], (k :: r2), _, _, hge2, _, heq => by
      have hpos : 1 ≤ sumFibIndices (k :: r2) := sum_pos_of_cons k r2 hge2
      rw [← heq] at hpos
      exact absurd hpos (by decide)
  | (i :: r1), [], hge1, _, _, _, heq => by
      have hpos : 1 ≤ sumFibIndices (i :: r1) := sum_pos_of_cons i r1 hge1
      rw [heq] at hpos
      exact absurd hpos (by decide)
  | (i :: r1), (k :: r2), hge1, hnc1, hge2, hnc2, heq => by
      have hik : i = k := heads_eq i k r1 r2 hge1 hnc1 hge2 hnc2 heq
      subst hik
      rw [sumFibIndices_cons, sumFibIndices_cons] at heq
      have hrest : sumFibIndices r1 = sumFibIndices r2 :=
        E213.Meta.Nat.NatRing213.nat_add_left_cancel heq
      have hge1' : AllGe2 r1 := hge1.2
      have hge2' : AllGe2 r2 := hge2.2
      have hnc1' : NonConsec r1 := by
        cases r1 with
        | nil => exact True.intro
        | cons a as => exact hnc1.2
      have hnc2' : NonConsec r2 := by
        cases r2 with
        | nil => exact True.intro
        | cons a as => exact hnc2.2
      have htail : r1 = r2 :=
        zeckendorf_unique r1 r2 hge1' hnc1' hge2' hnc2' hrest
      rw [htail]

/-- ★★★ **Zeckendorf uniqueness** (named-hypothesis form). -/
theorem zeckendorf_unique' (L1 L2 : List Nat)
    (h1 : AllGe2 L1) (hnc1 : NonConsec L1)
    (h2 : AllGe2 L2) (hnc2 : NonConsec L2)
    (heq : sumFibIndices L1 = sumFibIndices L2) : L1 = L2 :=
  zeckendorf_unique L1 L2 h1 hnc1 h2 hnc2 heq

/-- Only `[6,3]` is the valid representation of `10`. -/
theorem smoke_unique :
    ∀ L, AllGe2 L → NonConsec L → sumFibIndices L = 10 → L = [6, 3] :=
  fun L hge hnc heq =>
    zeckendorf_unique L [6, 3] hge hnc
      ⟨by decide, by decide, True.intro⟩ ⟨by decide, True.intro⟩
      (by rw [heq]; rfl)

end E213.Lib.Math.Combinatorics.ZeckendorfUniqueness
