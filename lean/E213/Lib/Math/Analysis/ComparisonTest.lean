import E213.Lib.Math.Analysis.UniformLimitContinuous
import E213.Lib.Math.Analysis.ModulusConvergence
import E213.Meta.Tactic.NatHelper

/-!
# Comparison test for series (∅-axiom, force-the-modulus)

For non-negative integer terms `a b : Nat → Nat` with `a k ≤ b k` for all `k`,
if the partial sums of `b` are Cauchy (in the `closeN`/`ConvergesWith` dyadic
sense) with a modulus, so are the partial sums of `a` — with the **same
modulus**.  The convergence rate transfers directly from the dominating series.

Reuses `closeN`/`distN` (`Analysis/UniformLimitContinuous`) and the
`prefixSum`/`segSum` telescoping idiom (`Combinatorics/ConsecutiveSumDvd`),
discharged in pure `Nat` via `NatHelper.add_sub_of_le`/`add_sub_cancel_right`.
-/

namespace E213.Lib.Math.Analysis.ComparisonTest

open E213.Lib.Math.Analysis.UniformLimitContinuous (distN closeN)

/-! ## 1. Partial sums and segment sums -/

/-- `psum a n = Σ_{k<n} a k` (Nat recursion). -/
def psum (a : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => psum a n + a n

/-- One partial-sum step is non-decreasing. -/
theorem psum_le_succ (a : Nat → Nat) (n : Nat) : psum a n ≤ psum a (n + 1) := by
  show psum a n ≤ psum a n + a n
  exact Nat.le_add_right _ _

/-- Partial sums are non-decreasing: `n ≤ m → psum a n ≤ psum a m`. -/
theorem psum_le_psum_of_le (a : Nat → Nat) :
    ∀ {n m : Nat}, n ≤ m → psum a n ≤ psum a m := by
  intro n m hnm
  induction m with
  | zero =>
      have h0 : n = 0 := Nat.le_antisymm hnm (Nat.zero_le _)
      rw [h0]; exact Nat.le_refl _
  | succ k ih =>
      rcases Nat.lt_or_ge n (k + 1) with hlt | hge
      · have hnk : n ≤ k := Nat.le_of_lt_succ hlt
        exact Nat.le_trans (ih hnk) (psum_le_succ a k)
      · have hnk : n = k + 1 := Nat.le_antisymm hnm hge
        rw [hnk]; exact Nat.le_refl _

/-- Alias matching the deliverable name. -/
theorem psum_mono (a : Nat → Nat) {n m : Nat} (h : n ≤ m) :
    psum a n ≤ psum a m := psum_le_psum_of_le a h

/-- Segment sum over the half-open range `[q, p)`, as the telescoping
    difference of partial sums. -/
def segSum (a : Nat → Nat) (q p : Nat) : Nat := psum a p - psum a q

/-- `segSum` is definitionally the prefix difference. -/
theorem segSum_eq_sub (a : Nat → Nat) (q p : Nat) :
    segSum a q p = psum a p - psum a q := rfl

/-! ## 2. The load-bearing monotonicity: `segSum_mono`

For `q ≤ p` and pointwise `a k ≤ b k`, the segment sum of `a` is dominated by
the segment sum of `b`.  We first prove the additive form
`psum a p = psum a q + segSum a q p` (telescoping), then bound the segment by
induction over the upper end. -/

/-- Telescoping additive form: `psum a q + segSum a q p = psum a p` for `q ≤ p`. -/
theorem psum_add_segSum (a : Nat → Nat) {q p : Nat} (hqp : q ≤ p) :
    psum a q + segSum a q p = psum a p := by
  show psum a q + (psum a p - psum a q) = psum a p
  exact E213.Tactic.NatHelper.add_sub_of_le (psum_le_psum_of_le a hqp)

/-- Segment sum unfolds one step on the upper end (for `q ≤ p`):
    `segSum a q (p+1) = segSum a q p + a p`. -/
theorem segSum_succ (a : Nat → Nat) {q p : Nat} (hqp : q ≤ p) :
    segSum a q (p + 1) = segSum a q p + a p := by
  -- segSum a q (p+1) = psum a (p+1) - psum a q = (psum a p + a p) - psum a q
  show psum a (p + 1) - psum a q = (psum a p - psum a q) + a p
  -- psum a (p+1) = psum a p + a p ; and psum a q ≤ psum a p
  have hle : psum a q ≤ psum a p := psum_le_psum_of_le a hqp
  -- (psum a p + a p) - psum a q  =  (psum a p - psum a q) + a p
  -- write psum a p = psum a q + d, d = psum a p - psum a q
  obtain ⟨d, hd⟩ := Nat.le.dest hle
  -- hd : psum a q + d = psum a p
  have hppd : psum a p - psum a q = d := by
    rw [← hd]
    show psum a q + d - psum a q = d
    -- psum a q + d - psum a q = d via add_sub: rewrite commutatively
    rw [Nat.add_comm (psum a q) d]
    exact E213.Tactic.NatHelper.add_sub_cancel_right d (psum a q)
  show psum a p + a p - psum a q = (psum a p - psum a q) + a p
  rw [hppd, ← hd]
  -- ((psum a q + d) + a p) - psum a q = d + a p
  rw [Nat.add_assoc (psum a q) d (a p), Nat.add_comm (psum a q) (d + a p)]
  exact E213.Tactic.NatHelper.add_sub_cancel_right (d + a p) (psum a q)

/-- **★ `segSum_mono` — the load-bearing monotonicity.**  Pointwise
    `a k ≤ b k` lifts to the segment sums: `segSum a q p ≤ segSum b q p`
    (for `q ≤ p`).  Induction over the upper end `p`. -/
theorem segSum_mono {a b : Nat → Nat} (hab : ∀ k, a k ≤ b k) :
    ∀ {q p : Nat}, q ≤ p → segSum a q p ≤ segSum b q p := by
  intro q p hqp
  induction p with
  | zero =>
      have hq0 : q = 0 := Nat.le_antisymm hqp (Nat.zero_le _)
      rw [hq0]
      -- segSum a 0 0 = psum a 0 - psum a 0 = 0
      show psum a 0 - psum a 0 ≤ psum b 0 - psum b 0
      rw [Nat.sub_self, Nat.sub_self]; exact Nat.le_refl 0
  | succ k ih =>
      rcases Nat.lt_or_ge q (k + 1) with hlt | hge
      · have hqk : q ≤ k := Nat.le_of_lt_succ hlt
        rw [segSum_succ a hqk, segSum_succ b hqk]
        exact Nat.add_le_add (ih hqk) (hab k)
      · have hqk : q = k + 1 := Nat.le_antisymm hqp hge
        rw [hqk]
        show psum a (k + 1) - psum a (k + 1) ≤ psum b (k + 1) - psum b (k + 1)
        rw [Nat.sub_self, Nat.sub_self]; exact Nat.le_refl 0

/-! ## 3. Distance = segment sum on a Cauchy interval

For `q ≤ p`, `distN (psum a q) (psum a p) = segSum a q p` because the partial
sums are non-decreasing (one leg of the truncated-subtraction distance is 0). -/

/-- `a ≤ b → a - b = 0` — ∅-axiom twin (Lean-core `Nat.sub_eq_zero_of_le`
    pulls `propext`; proved by induction, pattern from `Int213/Core`). -/
theorem sub_eq_zero_of_le_p : ∀ {a b : Nat}, a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a' + 1, b' + 1, h => by
      show (a' + 1) - (b' + 1) = 0
      rw [Nat.succ_sub_succ_eq_sub]
      exact sub_eq_zero_of_le_p (Nat.le_of_succ_le_succ h)

/-- For `q ≤ p`, the `distN` between the two partial sums is exactly the
    segment sum. -/
theorem distN_psum_eq_segSum (a : Nat → Nat) {q p : Nat} (hqp : q ≤ p) :
    distN (psum a q) (psum a p) = segSum a q p := by
  -- distN x y = (x - y) + (y - x); here x = psum a q ≤ psum a p = y
  show (psum a q - psum a p) + (psum a p - psum a q) = psum a p - psum a q
  have hle : psum a q ≤ psum a p := psum_le_psum_of_le a hqp
  have hz : psum a q - psum a p = 0 := sub_eq_zero_of_le_p hle
  rw [hz, Nat.zero_add]

/-! ## 4. ★★ The headline: comparison test on `closeN` -/

/-- **★★ `comparison_test` — the comparison test for series (∅-axiom).**

    If `a k ≤ b k` pointwise, and the partial sums of the dominating series
    `b` are `closeN`-Cauchy with modulus `r` (denominator scale `L0`), then the
    partial sums of `a` are `closeN`-Cauchy with the **same** modulus `r` and
    the **same** scale `L0`.  The convergence rate transfers directly.

    Proof: for `r m ≤ q ≤ p`, `closeN L0 m (psum a q) (psum a p)` unfolds to
    `2^m · distN(psum a q)(psum a p) < 2^(L0+1)`.  Since `q ≤ p`,
    `distN(psum a q)(psum a p) = segSum a q p ≤ segSum b q p
      = distN(psum b q)(psum b p)`, and multiplying by `2^m` preserves the
    bound (`Nat.mul_le_mul_left` then `Nat.lt_of_le_of_lt`). -/
theorem comparison_test {a b : Nat → Nat} {L0 : Nat} {r : Nat → Nat}
    (hab : ∀ k, a k ≤ b k)
    (hcauchy : ∀ m p q, r m ≤ q → q ≤ p → closeN L0 m (psum b q) (psum b p)) :
    ∀ m p q, r m ≤ q → q ≤ p → closeN L0 m (psum a q) (psum a p) := by
  intro m p q hrq hqp
  -- the dominating bound on the same interval
  have hb : closeN L0 m (psum b q) (psum b p) := hcauchy m p q hrq hqp
  -- distance for a ≤ distance for b
  have hdist : distN (psum a q) (psum a p) ≤ distN (psum b q) (psum b p) := by
    rw [distN_psum_eq_segSum a hqp, distN_psum_eq_segSum b hqp]
    exact segSum_mono hab hqp
  -- multiply by 2^m and chain with the dominating strict bound
  show 2 ^ m * distN (psum a q) (psum a p) < 2 ^ (L0 + 1)
  have hmul : 2 ^ m * distN (psum a q) (psum a p)
      ≤ 2 ^ m * distN (psum b q) (psum b p) :=
    Nat.mul_le_mul_left _ hdist
  exact Nat.lt_of_le_of_lt hmul hb

/-! ## 5. Non-vacuous instantiations

(i) The trivial `a = b` case: any `closeN`-Cauchy series compares to itself.
(ii) A dominated eventually-zero pair: `a k = 0`, `b k = k`.  Then `a ≤ b`,
     and the partial sums of `a` are constantly `0`, so they are `closeN`-Cauchy
     with modulus `0` at any scale — derivable directly from `comparison_test`
     once a (trivial) bound on `b`'s sums is supplied. -/

/-- (i) `a = b`: the comparison test is reflexive. -/
theorem comparison_test_refl {b : Nat → Nat} {L0 : Nat} {r : Nat → Nat}
    (hcauchy : ∀ m p q, r m ≤ q → q ≤ p → closeN L0 m (psum b q) (psum b p)) :
    ∀ m p q, r m ≤ q → q ≤ p → closeN L0 m (psum b q) (psum b p) :=
  comparison_test (fun _ => Nat.le_refl _) hcauchy

/-- A pointwise-dominated eventually-zero term: `a k = 0 ≤ b k`. -/
theorem zero_dominated (b : Nat → Nat) : ∀ k, (fun _ : Nat => 0) k ≤ b k :=
  fun _ => Nat.zero_le _

/-- (ii) The zero series `a = 0` has constant partial sums `0`, hence is
    `closeN`-Cauchy with modulus `0` at scale `L0` for free — and this is
    exactly what `comparison_test` produces from *any* dominating Cauchy `b`. -/
theorem zero_series_cauchy (L0 : Nat) :
    ∀ m p q, (fun _ : Nat => 0) m ≤ q → q ≤ p →
      closeN L0 m (psum (fun _ : Nat => 0) q) (psum (fun _ : Nat => 0) p) := by
  intro m p q _ hqp
  -- psum 0 n = 0 for all n, so distN = 0 and 2^m·0 = 0 < 2^(L0+1)
  show 2 ^ m * distN (psum (fun _ : Nat => 0) q) (psum (fun _ : Nat => 0) p)
      < 2 ^ (L0 + 1)
  have hpz : ∀ n, psum (fun _ : Nat => 0) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
        show psum (fun _ : Nat => 0) k + 0 = 0
        rw [ih]
  rw [hpz q, hpz p]
  -- distN 0 0 = 0
  show 2 ^ m * ((0 - 0) + (0 - 0)) < 2 ^ (L0 + 1)
  rw [Nat.sub_self, Nat.add_zero, Nat.mul_zero]
  exact Nat.pos_pow_of_pos (L0 + 1) (by decide)

/-! ## 6. Smoke test (closed numerals) -/

def smokeA : Nat → Nat := fun k => k       -- 0,1,2,...
def smokeB : Nat → Nat := fun k => 2 * k   -- dominates smokeA

example : psum smokeA 3 = 3 := rfl          -- 0+1+2
example : psum smokeB 3 = 6 := rfl          -- 0+2+4
example : segSum smokeA 1 3 = 3 := rfl      -- (0+1+2) - 0 = 3 ; psum 1 = 0
example : segSum smokeB 1 3 = 6 := rfl

#print axioms psum
#print axioms segSum_mono
#print axioms psum_mono
#print axioms psum_le_psum_of_le
#print axioms comparison_test
#print axioms zero_series_cauchy

end E213.Lib.Math.Analysis.ComparisonTest
