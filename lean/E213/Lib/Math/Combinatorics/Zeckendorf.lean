import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# Zeckendorf's theorem — existence (∅-axiom)

★ **`zeckendorf`**: every natural `n` is a sum of Fibonacci numbers with indices
`≥ 2`, no two of consecutive index — Zeckendorf's representation, the existence
direction, **constructively** and ∅-axiom.

The proof is the greedy algorithm with its non-consecutiveness invariant:

  * `greedy_gap` (the heart) — if `fib(k+1) ≤ n < fib(k+2)` then the residual
    `n − fib(k+1) < fib k`, so the next Fibonacci used has index `≤ k−1`: a gap of
    `≥ 2`.  (From `fib(k+2) = fib k + fib(k+1)`.)
  * `find_max` / `exists_max_index` — the maximal index `j ≥ 2` with
    `fib j ≤ n < fib(j+1)` (downward search as induction on a ceiling offset).
  * `prepend_valid` — prepending the greedy `j` preserves `AllGe2`/`NonConsec`
    (the head `i` of the residual list has `fib i ≤ r < fib(j−1)`, so `i+2 ≤ j`).
  * `zeckCore` — fuel-induction greedy: each step drops the residual strictly, so
    fuel decreases (the corpus's PURE substitute for well-founded recursion).

Existence only — uniqueness is a separate, harder induction (left open).  `fib`
is a module-local two-step recurrence (corpus convention; consolidating the
several local `fib` defs is a known smell, deferred).  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.Zeckendorf

open E213.Tactic.NatHelper (sub_lt_sub_right add_sub_cancel_right sub_add_cancel)

/-- Standard Fibonacci: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_rec (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-! ## The greedy-gap inequality (the mathematical heart) -/

/-- ★ **Greedy-gap inequality.**  If `fib (k+1) ≤ n < fib (k+2)` then the greedy
    residual `n - fib (k+1)` is strictly below `fib k` — exactly the invariant that
    forces Zeckendorf non-consecutiveness (after subtracting `fib(k+1)`, the remainder
    is too small to contain `fib k`, so the next index is `≤ k−1`). -/
theorem greedy_gap {k n : Nat}
    (hlo : fib (k + 1) ≤ n) (hhi : n < fib (k + 2)) :
    n - fib (k + 1) < fib k := by
  have hhi' : n < fib k + fib (k + 1) := by
    rw [fib_rec] at hhi; exact hhi
  have step : n - fib (k + 1) < (fib k + fib (k + 1)) - fib (k + 1) :=
    sub_lt_sub_right (fib (k + 1)) hlo hhi'
  have hcancel : (fib k + fib (k + 1)) - fib (k + 1) = fib k :=
    add_sub_cancel_right (fib k) (fib (k + 1))
  rw [hcancel] at step
  exact step

/-! ## Fibonacci sums over index lists + the validity predicates -/

/-- Sum of `fib` over a list of indices. -/
def sumFibIndices : List Nat → Nat
  | []      => 0
  | i :: is => fib i + sumFibIndices is

theorem sumFibIndices_cons (i : Nat) (is : List Nat) :
    sumFibIndices (i :: is) = fib i + sumFibIndices is := rfl

/-- Every index in the list is `≥ 2` (indices `2,3,4,…` = values `1,2,3,5,…`). -/
def AllGe2 : List Nat → Prop
  | []      => True
  | i :: is => 2 ≤ i ∧ AllGe2 is

/-- **Non-consecutive**: adjacent indices differ by `≥ 2` (no two adjacent Fibonacci
    numbers are both used). -/
def NonConsec : List Nat → Prop
  | []            => True
  | _ :: []       => True
  | i :: j :: rest => j + 2 ≤ i ∧ NonConsec (j :: rest)

/-! ## Monotonicity / growth facts about `fib` -/

/-- `fib k ≤ fib (k+1)`. -/
theorem fib_le_succ : ∀ k : Nat, fib k ≤ fib (k + 1)
  | 0 => Nat.zero_le _
  | 1 => Nat.le_refl 1
  | k + 2 => by
      rw [show fib (k + 3) = fib (k + 1) + fib (k + 2) from fib_rec (k + 1)]
      exact Nat.le_add_left (fib (k + 2)) (fib (k + 1))

/-- Weak monotonicity: `a ≤ b → fib a ≤ fib b`. -/
theorem fib_mono {a b : Nat} (h : a ≤ b) : fib a ≤ fib b := by
  induction b with
  | zero =>
      have : a = 0 := Nat.le_zero.mp h
      rw [this]; exact Nat.le_refl _
  | succ k ih =>
      rcases Nat.lt_or_ge a (k + 1) with hlt | hge
      · exact Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) (fib_le_succ k)
      · have : a = k + 1 := Nat.le_antisymm h hge
        rw [this]; exact Nat.le_refl _

/-- `1 ≤ fib (k+1)`. -/
theorem one_le_fib_succ : ∀ k : Nat, 1 ≤ fib (k + 1)
  | 0 => Nat.le_refl 1
  | k + 1 => by
      rw [show fib (k + 2) = fib k + fib (k + 1) from fib_rec k]
      exact Nat.le_trans (one_le_fib_succ k) (Nat.le_add_left _ _)

/-- `2 ≤ fib (n+3)`. -/
theorem two_le_fib_add_three (n : Nat) : 2 ≤ fib (n + 3) := by
  rw [show fib (n + 3) = fib (n + 1) + fib (n + 2) from fib_rec (n + 1)]
  exact Nat.add_le_add (one_le_fib_succ n) (one_le_fib_succ (n + 1))

/-- `n < fib (n+2)`. -/
theorem n_lt_fib : ∀ n : Nat, n < fib (n + 2)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      have ih1 : n < fib (n + 2) := n_lt_fib n
      rw [show fib (n + 4) = fib (n + 2) + fib (n + 3) from fib_rec (n + 2)]
      have a1 : n + 1 ≤ fib (n + 2) := ih1
      have a2 : 2 ≤ fib (n + 3) := two_le_fib_add_three n
      have hsum : (n + 1) + 2 ≤ fib (n + 2) + fib (n + 3) := Nat.add_le_add a1 a2
      have : n + 2 + 1 ≤ fib (n + 2) + fib (n + 3) := by
        rw [show n + 2 + 1 = (n + 1) + 2 from by ring_nat]; exact hsum
      exact this

theorem fib_two : fib 2 = 1 := rfl

/-! ## Maximal-index finder: largest `j ≥ 2` with `fib j ≤ n < fib (j+1)` -/

/-- For `n ≥ 1` with a ceiling `n < fib (c+3)`, the largest index `j ≥ 2` with
    `fib j ≤ n < fib (j+1)` exists (downward search as induction on `c`). -/
theorem find_max : ∀ (c n : Nat), fib 2 ≤ n → n < fib (c + 3) →
    ∃ j, 2 ≤ j ∧ fib j ≤ n ∧ n < fib (j + 1)
  | 0, n, hlo, hhi => by
      refine ⟨2, Nat.le_refl 2, hlo, ?_⟩
      show n < fib 3
      exact hhi
  | c + 1, n, hlo, hhi => by
      rcases Nat.lt_or_ge n (fib (c + 3)) with hlt | hge
      · exact find_max c n hlo hlt
      · refine ⟨c + 3, ?_, hge, ?_⟩
        · exact Nat.le_add_left 2 (c + 1)
        · show n < fib (c + 4)
          exact hhi

/-- Wrapper: any `n ≥ 1` has a maximal Fibonacci index (ceiling from `n_lt_fib`). -/
theorem exists_max_index {n : Nat} (hn : 1 ≤ n) :
    ∃ j, 2 ≤ j ∧ fib j ≤ n ∧ n < fib (j + 1) := by
  have hlo : fib 2 ≤ n := by rw [fib_two]; exact hn
  have hceil : n < fib (n + 3) :=
    Nat.lt_of_lt_of_le (n_lt_fib n) (fib_mono (Nat.le_succ (n + 2)))
  exact find_max n n hlo hceil

/-! ## Full Zeckendorf existence (non-consecutive) -/

/-- `fib` of the head is `≤` the list's Fibonacci sum. -/
theorem head_fib_le_sum (i : Nat) (is : List Nat) :
    fib i ≤ sumFibIndices (i :: is) := by
  rw [sumFibIndices_cons]
  exact Nat.le_add_right (fib i) (sumFibIndices is)

/-- From `fib a < fib b` conclude `a < b` (contrapositive of weak monotonicity). -/
theorem lt_of_fib_lt {a b : Nat} (h : fib a < fib b) : a < b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd (fib_mono hge) (Nat.not_le_of_gt h)

/-- **Prepend lemma.**  If `L` is valid with sum `r`, and `r < fib (j−1)` with
    `2 ≤ j`, then `j :: L` is valid: the head `i` of `L` has `fib i ≤ r < fib(j−1)`,
    so `i < j−1`, so `i+2 ≤ j`. -/
theorem prepend_valid {j r : Nat} {L : List Nat}
    (hj : 2 ≤ j)
    (hsum : sumFibIndices L = r)
    (hge2 : AllGe2 L) (hnc : NonConsec L)
    (hgap : r < fib (j - 1)) :
    AllGe2 (j :: L) ∧ NonConsec (j :: L) := by
  refine ⟨⟨hj, hge2⟩, ?_⟩
  cases L with
  | nil => exact True.intro
  | cons i is =>
      have hi_le_r : fib i ≤ r := by
        rw [← hsum]; exact head_fib_le_sum i is
      have hfi_lt : fib i < fib (j - 1) := Nat.lt_of_le_of_lt hi_le_r hgap
      have hi_lt : i < j - 1 := lt_of_fib_lt hfi_lt
      have hj1 : (j - 1) + 1 = j := by
        have : 1 ≤ j := Nat.le_trans (by decide) hj
        exact sub_add_cancel this
      have step2 : i + 1 + 1 ≤ (j - 1) + 1 := Nat.add_le_add_right hi_lt 1
      have step3 : i + 2 ≤ j := by
        rw [show i + 1 + 1 = i + 2 from by ring_nat, hj1] at step2; exact step2
      exact ⟨step3, hnc⟩

/-- **Core greedy existence (fuel-induction).**  For every `n ≤ fuel`, a
    non-consecutive list of Fibonacci indices (`≥ 2`) sums to `n`.  Each greedy step
    replaces `n` by `r = n − fib j < n`, so `fuel` decreases. -/
theorem zeckCore : ∀ (fuel n : Nat), n ≤ fuel →
    ∃ L, sumFibIndices L = n ∧ AllGe2 L ∧ NonConsec L
  | 0, n, hle => by
      have : n = 0 := Nat.le_zero.mp hle
      exact ⟨[], by rw [this]; rfl, True.intro, True.intro⟩
  | fuel + 1, n, hle => by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · exact ⟨[], by rw [hn0]; rfl, True.intro, True.intro⟩
      · obtain ⟨j, hj2, hjle, hjgt⟩ := exists_max_index hnpos
        have hj1 : (j - 1) + 1 = j := by
          have : 1 ≤ j := Nat.le_trans (by decide) hj2
          exact sub_add_cancel this
        have hlo' : fib ((j - 1) + 1) ≤ n := by rw [hj1]; exact hjle
        have hhi' : n < fib ((j - 1) + 2) := by
          have heq : (j - 1) + 2 = j + 1 := by
            rw [show (j - 1) + 2 = ((j - 1) + 1) + 1 from by ring_nat, hj1]
          rw [heq]; exact hjgt
        have hgap : n - fib j < fib (j - 1) := by
          have := greedy_gap (k := j - 1) hlo' hhi'
          rw [hj1] at this; exact this
        have hfib_pos : 1 ≤ fib j := by
          have : fib 2 ≤ fib j := fib_mono hj2
          rw [fib_two] at this; exact this
        have hr_lt_n : n - fib j < n := Nat.sub_lt hnpos hfib_pos
        have hr_le_fuel : n - fib j ≤ fuel :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr_lt_n hle)
        obtain ⟨L', hsum', hge2', hnc'⟩ := zeckCore fuel (n - fib j) hr_le_fuel
        obtain ⟨hge2'', hnc''⟩ := prepend_valid hj2 hsum' hge2' hnc' hgap
        refine ⟨j :: L', ?_, hge2'', hnc''⟩
        rw [sumFibIndices_cons, hsum']
        exact E213.Tactic.NatHelper.add_sub_of_le hjle

/-- ★★★ **Zeckendorf existence (full, non-consecutive).**  Every natural `n` is the
    sum of Fibonacci numbers with indices `≥ 2`, no two of consecutive index. -/
theorem zeckendorf (n : Nat) :
    ∃ L, sumFibIndices L = n ∧ AllGe2 L ∧ NonConsec L :=
  zeckCore n n (Nat.le_refl n)

/-! ## Smoke checks — the predicates are non-vacuous and reject consecutive indices. -/

/-- `10 = 8 + 2 = fib 6 + fib 3` (indices `6,3`: gap `3 ≥ 2`). -/
theorem smoke_sum : sumFibIndices [6, 3] = 10 := by decide
theorem smoke_ge2 : AllGe2 [6, 3] := ⟨by decide, by decide, True.intro⟩
theorem smoke_nc  : NonConsec [6, 3] := ⟨by decide, True.intro⟩
/-- A consecutive list is correctly rejected (`NonConsec [4,3]` needs `5 ≤ 4`). -/
theorem smoke_nc_reject : ¬ NonConsec [4, 3] := fun h => absurd h.1 (by decide)

end E213.Lib.Math.Combinatorics.Zeckendorf
