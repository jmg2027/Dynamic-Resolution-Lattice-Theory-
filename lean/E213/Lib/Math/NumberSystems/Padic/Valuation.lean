import E213.Lib.Math.NumberSystems.Padic.Arith

/-!
# Real213-p-adic Valuation (Phase 3)

The p-adic valuation `v_p(x)` is the position of the first non-zero
digit in the base-p expansion of `x ∈ ℤ_p`.  Equivalently, `v_p(x)`
is the largest `n` such that `p^n` divides `x` (for non-zero x).

In our finite-truncation framework, we define `vAt x N` — the
valuation restricted to the first `N` digits:
  · If the first non-zero digit is at position k < N, return k.
  · If all first N digits are zero, return N.

This avoids the "v_p(0) = ∞" issue: for any finite truncation level,
the valuation is a well-defined Nat.

## Phase 3 contents

  · `vAtAcc x start n` — accumulator-style search from position start
    over the next n positions
  · `vAt x N` — bounded valuation over range [0, N)
  · Smokes: zero, one, neg_one valuation values
  · `vAt_zero` and `vAt_one_pos` characterization theorems
-/

namespace E213.Lib.Math.NumberSystems.Padic.Valuation

open E213.Lib.Math.NumberSystems.Padic (ZpSeq)

/-! ## Accumulator-style search -/

/-- Search positions `[start, start + n)` for the first non-zero
    digit of `x`.  Returns the position of the first non-zero,
    or `start + n` if all positions in range are zero. -/
def vAtAcc {p : Nat} (x : ZpSeq p) (start : Nat) : Nat → Nat
  | 0 => start
  | n + 1 =>
      if (x.digits start).val = 0 then
        vAtAcc x (start + 1) n
      else
        start

/-- p-adic valuation bounded to `N` digits.  Search over [0, N). -/
def vAt {p : Nat} (x : ZpSeq p) (N : Nat) : Nat := vAtAcc x 0 N

/-! ## Zero sequence has maximum valuation -/

/-- Searching all-zero positions at any starting point: the search
    exhausts to `start + n`. -/
theorem vAtAcc_all_zero {p : Nat} (hp : 0 < p) :
    ∀ start n, vAtAcc (ZpSeq.zero p hp) start n = start + n
  | start, 0 => by show start = start + 0; rfl
  | start, n + 1 => by
    show (if ((ZpSeq.zero p hp).digits start).val = 0
          then vAtAcc (ZpSeq.zero p hp) (start + 1) n
          else start) = start + (n + 1)
    have hz : ((ZpSeq.zero p hp).digits start).val = 0 := rfl
    rw [if_pos hz]
    rw [vAtAcc_all_zero hp (start + 1) n]
    -- Goal: (start + 1) + n = start + (n + 1)
    rw [Nat.add_assoc, Nat.add_comm 1 n]

/-- `vAt (zero p) N = N`: the zero sequence has all-N valuation. -/
theorem vAt_zero {p : Nat} (hp : 0 < p) (N : Nat) :
    vAt (ZpSeq.zero p hp) N = N := by
  show vAtAcc (ZpSeq.zero p hp) 0 N = N
  rw [vAtAcc_all_zero hp 0 N]
  exact Nat.zero_add N

/-! ## One sequence has zero valuation -/

/-- `vAt (one p) N = 0` for N ≥ 1: the one sequence has first digit
    non-zero, so the valuation is 0. -/
theorem vAt_one_pos {p : Nat} (hp : 1 < p) (N : Nat) (hN : 0 < N) :
    vAt (ZpSeq.one p hp) N = 0 := by
  match N, hN with
  | N + 1, _ =>
    show vAtAcc (ZpSeq.one p hp) 0 (N + 1) = 0
    show (if ((ZpSeq.one p hp).digits 0).val = 0
          then vAtAcc (ZpSeq.one p hp) 1 N
          else 0) = 0
    have hone : ((ZpSeq.one p hp).digits 0).val = 1 := rfl
    rw [if_neg]
    intro h
    rw [hone] at h
    exact absurd h (by decide)

/-! ## neg_one valuation -/

/-- `vAt (neg_one p) N = 0` for N ≥ 1 and p ≥ 2: neg_one has all
    digits = p-1 ≠ 0 (when p ≥ 2). -/
theorem vAt_neg_one_pos {p : Nat} (hp : 1 < p) (N : Nat) (hN : 0 < N) :
    vAt (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)) N = 0 := by
  match N, hN with
  | N + 1, _ =>
    show vAtAcc (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)) 0 (N + 1) = 0
    show (if ((ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)).digits 0).val = 0
          then vAtAcc (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)) 1 N
          else 0) = 0
    have hng : ((ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)).digits 0).val = p - 1 := rfl
    rw [if_neg]
    intro h
    rw [hng] at h
    -- h : p - 1 = 0, but hp : 1 < p
    -- Cases on p: 0 ⊥ via hp; 1 ⊥ via hp; q+2 → h becomes q+1 = 0 which is impossible
    match p, hp, h with
    | 0, hp', _ => exact absurd hp' (Nat.not_lt_zero _)
    | 1, hp', _ => exact absurd hp' (by decide)
    | _ + 2, _, hq => exact Nat.noConfusion hq

/-! ## Per-prime smokes -/

/-- p = 5: vAt of zero at level 3 is 3. -/
theorem smoke_vAt_zero_p5 :
    vAt (ZpSeq.zero 5 (by decide)) 3 = 3 :=
  vAt_zero (by decide) 3

/-- p = 5: vAt of one at level 3 is 0. -/
theorem smoke_vAt_one_p5 :
    vAt (ZpSeq.one 5 (by decide)) 3 = 0 :=
  vAt_one_pos (by decide) 3 (by decide)

/-- p = 5: vAt of neg_one at level 3 is 0. -/
theorem smoke_vAt_neg_one_p5 :
    vAt (ZpSeq.neg_one 5 (by decide)) 3 = 0 :=
  vAt_neg_one_pos (by decide) 3 (by decide)

/-- p = 7: vAt of zero at level 5 is 5. -/
theorem smoke_vAt_zero_p7 :
    vAt (ZpSeq.zero 7 (by decide)) 5 = 5 :=
  vAt_zero (by decide) 5

/-! ## Phase 3 capstone -/

/-- ★★★★★ **Phase 3: p-adic valuation closed**

  Provides bounded p-adic valuation `vAt x N` returning the position
  of the first non-zero digit in the range [0, N), or N if all are
  zero.

  Verified behaviour on canonical p-adic sequences:
    · `vAt (zero p) N = N` (zero sequence has maximum valuation)
    · `vAt (one p) N = 0` for N ≥ 1 (one sequence has first-digit
      valuation 0)
    · `vAt (neg_one p) N = 0` for N ≥ 1, p ≥ 2 (neg_one all digits
      ≠ 0)

  The bounded form sidesteps the "v_p(0) = ∞" issue: for any finite
  truncation, the valuation is a Nat. -/
theorem phase3_valuation_close :
    -- Zero sequence: vAt = N at p = 5
    vAt (ZpSeq.zero 5 (by decide)) 3 = 3
    ∧ vAt (ZpSeq.zero 5 (by decide)) 10 = 10
    -- One sequence: vAt = 0 at p ∈ {2, 3, 5, 7}
    ∧ vAt (ZpSeq.one 2 (by decide)) 3 = 0
    ∧ vAt (ZpSeq.one 3 (by decide)) 3 = 0
    ∧ vAt (ZpSeq.one 5 (by decide)) 3 = 0
    ∧ vAt (ZpSeq.one 7 (by decide)) 3 = 0
    -- neg_one: vAt = 0 at p ∈ {3, 5, 7}
    ∧ vAt (ZpSeq.neg_one 3 (by decide)) 3 = 0
    ∧ vAt (ZpSeq.neg_one 5 (by decide)) 3 = 0
    ∧ vAt (ZpSeq.neg_one 7 (by decide)) 3 = 0
    -- Definitional: vAt 0 = 0 (empty range)
    ∧ vAt (ZpSeq.zero 5 (by decide)) 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · exact vAt_zero (by decide) 3
  · exact vAt_zero (by decide) 10
  · exact vAt_one_pos (by decide) 3 (by decide)
  · exact vAt_one_pos (by decide) 3 (by decide)
  · exact vAt_one_pos (by decide) 3 (by decide)
  · exact vAt_one_pos (by decide) 3 (by decide)
  · exact vAt_neg_one_pos (by decide) 3 (by decide)
  · exact vAt_neg_one_pos (by decide) 3 (by decide)
  · exact vAt_neg_one_pos (by decide) 3 (by decide)

end E213.Lib.Math.NumberSystems.Padic.Valuation
