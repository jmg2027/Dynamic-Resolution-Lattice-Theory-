import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

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

/-! ## §4 — characterisation, monotonicity, perfect squares, dyadic refinement -/

/-- ★★ **Defining property**: `k² ≤ n ⟹ k ≤ isqrt n` (`isqrt n` is the *largest* such `k`). -/
theorem le_isqrt_of_sq_le (k n : Nat) (h : k * k ≤ n) : k ≤ isqrt n := by
  rcases Nat.lt_or_ge (isqrt n) k with hc | hge
  · exfalso
    have hsq : (isqrt n + 1) * (isqrt n + 1) ≤ k * k :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hc) (Nat.succ_le_of_lt hc)
    exact absurd (Nat.lt_of_lt_of_le (isqrt_bracket n).2 (Nat.le_trans hsq h)) (Nat.lt_irrefl n)
  · exact hge

/-- ★ **Monotonicity**: `m ≤ n ⟹ isqrt m ≤ isqrt n`. -/
theorem isqrt_mono {m n : Nat} (h : m ≤ n) : isqrt m ≤ isqrt n :=
  le_isqrt_of_sq_le (isqrt m) n (Nat.le_trans (isqrt_sq_le m) h)

/-- ★ **Perfect square**: `isqrt (k·k) = k`. -/
theorem isqrt_perfect (k : Nat) : isqrt (k * k) = k := by
  have hle : k ≤ isqrt (k * k) := le_isqrt_of_sq_le k (k * k) (Nat.le_refl _)
  have hge : isqrt (k * k) ≤ k := by
    rcases Nat.lt_or_ge (isqrt (k * k)) (k + 1) with h | h
    · exact Nat.le_of_lt_succ h
    · exfalso
      have hsq : (k + 1) * (k + 1) ≤ isqrt (k * k) * isqrt (k * k) := Nat.mul_le_mul h h
      have hkk : k * k < (k + 1) * (k + 1) := by
        have e : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring_nat
        rw [e]; exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      exact absurd (Nat.lt_of_lt_of_le hkk (Nat.le_trans hsq (isqrt_sq_le (k * k)))) (Nat.lt_irrefl _)
  exact Nat.le_antisymm hge hle

/-- ★★★ **Dyadic refinement**: `2·isqrt n ≤ isqrt (4n) ≤ 2·isqrt n + 1`.  Doubling the
    resolution (`n ↦ 4n`, i.e. `√n ↦ 2√n`) adds at most one unit of error — the convergence-rate
    certificate making the dyadic sequence `isqrt(a·4ᵏ)/2ᵏ → √a` Cauchy. -/
theorem isqrt_four_mul (n : Nat) :
    2 * isqrt n ≤ isqrt (4 * n) ∧ isqrt (4 * n) ≤ 2 * isqrt n + 1 := by
  refine ⟨?_, ?_⟩
  · -- lower: (2·isqrt n)² = 4·(isqrt n)² ≤ 4n
    refine le_isqrt_of_sq_le (2 * isqrt n) (4 * n) ?_
    have e : (2 * isqrt n) * (2 * isqrt n) = 4 * (isqrt n * isqrt n) := by ring_nat
    rw [e]; exact Nat.mul_le_mul_left 4 (isqrt_sq_le n)
  · -- upper: else (2·isqrt n+2)² ≤ (isqrt 4n)² ≤ 4n < 4(isqrt n+1)² = (2·isqrt n+2)²
    rcases Nat.lt_or_ge (isqrt (4 * n)) (2 * isqrt n + 2) with h | h
    · exact Nat.le_of_lt_succ h
    · exfalso
      have hsq : (2 * isqrt n + 2) * (2 * isqrt n + 2) ≤ isqrt (4 * n) * isqrt (4 * n) :=
        Nat.mul_le_mul h h
      have h4n : 4 * n < (2 * isqrt n + 2) * (2 * isqrt n + 2) := by
        have hb : n < (isqrt n + 1) * (isqrt n + 1) := (isqrt_bracket n).2
        have e : (2 * isqrt n + 2) * (2 * isqrt n + 2) = 4 * ((isqrt n + 1) * (isqrt n + 1)) := by
          ring_nat
        rw [e]
        have hb' : 4 * (n + 1) ≤ 4 * ((isqrt n + 1) * (isqrt n + 1)) := Nat.mul_le_mul_left 4 hb
        have hstep : 4 * n < 4 * (n + 1) := by
          have e2 : 4 * (n + 1) = 4 * n + 4 := by ring_nat
          rw [e2]; exact Nat.lt_add_of_pos_right (by decide)
        exact Nat.lt_of_lt_of_le hstep hb'
      exact absurd (Nat.lt_of_lt_of_le h4n (Nat.le_trans hsq (isqrt_sq_le (4 * n)))) (Nat.lt_irrefl _)

end E213.Lib.Math.NumberTheory.IntSqrt
