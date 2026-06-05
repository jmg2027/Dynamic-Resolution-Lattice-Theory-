import E213.Meta.Tactic.NatHelper

/-!
# Integer (floor) square root `isqrt` (∅-axiom)

`isqrt n` = the largest `k` with `k² ≤ n` — the discrete foundation of the real `sqrt`
(marathon T4): `Real213` `sqrt` is the `Real213` limit of `isqrt` of finer and finer dyadic
rescalings.  Built by a downward scan (`isqrtAux`) with the correctness **bracket**

  `isqrt n · isqrt n ≤ n  <  (isqrt n + 1)²`

so `isqrt n` is genuinely `⌊√n⌋`.  Pure `Nat`, no `Decidable`-via-`propext` leakage (the scan
uses `Nat.decLe` through `if`, kernel-reduced).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.IntSqrt

/-- Downward scan: the largest `k ≤ c` with `k² ≤ n` (always returns ≤ c, and `0` works since
    `0 ≤ n`). -/
def isqrtAux (n : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => if (c + 1) * (c + 1) ≤ n then c + 1 else isqrtAux n c

/-- `isqrt n = ⌊√n⌋`, found by scanning down from `n`. -/
def isqrt (n : Nat) : Nat := isqrtAux n n

/-! ## §1 — lower bound and range -/

/-- `isqrtAux n c` is `≤ c`. -/
theorem isqrtAux_le (n : Nat) : ∀ c, isqrtAux n c ≤ c
  | 0 => Nat.le_refl 0
  | c + 1 => by
    show (if (c + 1) * (c + 1) ≤ n then c + 1 else isqrtAux n c) ≤ c + 1
    by_cases h : (c + 1) * (c + 1) ≤ n
    · rw [if_pos h]; exact Nat.le_refl _
    · rw [if_neg h]; exact Nat.le_trans (isqrtAux_le n c) (Nat.le_succ c)

/-- ★ **Lower bound**: `isqrtAux n c · isqrtAux n c ≤ n`. -/
theorem isqrtAux_sq_le (n : Nat) : ∀ c, isqrtAux n c * isqrtAux n c ≤ n
  | 0 => by show 0 * 0 ≤ n; rw [Nat.zero_mul]; exact Nat.zero_le n
  | c + 1 => by
    show (if (c + 1) * (c + 1) ≤ n then c + 1 else isqrtAux n c)
          * (if (c + 1) * (c + 1) ≤ n then c + 1 else isqrtAux n c) ≤ n
    by_cases h : (c + 1) * (c + 1) ≤ n
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact isqrtAux_sq_le n c

/-! ## §2 — maximality (upper bound) -/

/-- **Maximality of the scan**: every candidate strictly above the result, up to `c`, fails
    (`n < j²`).  Precisely: if `isqrtAux n c < j` and `j ≤ c` then `n < j · j`. -/
theorem isqrtAux_max (n : Nat) :
    ∀ c j, isqrtAux n c < j → j ≤ c → n < j * j
  | 0, j, hlt, hjc => absurd (Nat.lt_of_lt_of_le hlt hjc) (Nat.lt_irrefl 0)
  | c + 1, j, hlt, hjc => by
    by_cases h : (c + 1) * (c + 1) ≤ n
    · -- result is c+1, so j > c+1 but j ≤ c+1: impossible
      rw [isqrtAux] at hlt
      rw [if_pos h] at hlt
      exact absurd hjc (Nat.not_le.mpr hlt)
    · -- result is isqrtAux n c; either j = c+1 (then h gives n < j²) or j ≤ c (IH)
      rw [isqrtAux, if_neg h] at hlt
      rcases Nat.lt_or_eq_of_le hjc with hjlt | hjeq
      · exact isqrtAux_max n c j hlt (Nat.le_of_lt_succ hjlt)
      · subst hjeq; exact Nat.not_le.mp h

/-! ## §3 — the floor-square-root bracket -/

/-- ★★ **Lower bound**: `isqrt n · isqrt n ≤ n`. -/
theorem isqrt_sq_le (n : Nat) : isqrt n * isqrt n ≤ n := isqrtAux_sq_le n n

/-- ★★★ **Floor square-root bracket**: `isqrt n · isqrt n ≤ n < (isqrt n + 1)²`.
    So `isqrt n = ⌊√n⌋` — the largest `k` with `k² ≤ n`. -/
theorem isqrt_bracket (n : Nat) :
    isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  refine ⟨isqrt_sq_le n, ?_⟩
  rcases Nat.lt_or_ge n 2 with hsmall | hbig
  · rcases E213.Tactic.NatHelper.cases_lt_two hsmall with h0 | h1
    · subst h0; decide
    · subst h1; decide
  · -- n ≥ 2 ⟹ isqrt n < n, so the maximality scan covers j = isqrt n + 1
    have hlt : isqrt n < n := by
      rcases Nat.lt_or_eq_of_le (isqrtAux_le n n) with h | h
      · exact h
      · exfalso
        have hsq : n * n ≤ n := by
          have := isqrt_sq_le n; rw [isqrt, h] at this; exact this
        have h2n : 2 * n ≤ n := Nat.le_trans (Nat.mul_le_mul_right n hbig) hsq
        have hnn : n + n ≤ n + 0 := by rw [Nat.add_zero, ← Nat.two_mul]; exact h2n
        have : n ≤ 0 := E213.Tactic.NatHelper.le_of_add_le_add_left hnn
        exact absurd (Nat.le_trans hbig this) (by decide)
    exact isqrtAux_max n n (isqrt n + 1) (Nat.lt_succ_self _) hlt

end E213.Lib.Math.NumberTheory.IntSqrt
