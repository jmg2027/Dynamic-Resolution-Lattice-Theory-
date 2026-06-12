import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# TwoThreeUnique — the proven linear floor of the tetration (`^`) wall

`2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d → a = c ∧ b = d`: the exponent vector
`(a, b)` of a `{2, 3}`-power is **unique**.  Read in the slot programme as
the *linear* fold-back absence — the ℕ-native statement that the two
log-branches (`vp 2`, `vp 3`) do **not** collapse into one another by any
linear identity.  Each prime power is its own coordinate; no carrying
between the `2`-axis and the `3`-axis exists.

This is the **proven floor** of the `^`-wall: the structural ceiling above
it (the transcendence / Schanuel-type statements about how *deep* the
tower folds — algebraic independence of iterated exponentials) is
explicitly **out of scope** here.  What is closed is the linear layer: the
absence of a non-trivial ℕ-linear relation among `2`- and `3`-powers.

Elementary route (no `vp`-multiplicativity invoked):

  * `three_pow_not_even` — `isEven (3 ^ b) = false` (bare induction: odd
    stays odd under `· * 3`).
  * `two_not_dvd_three_pow` — `¬ 2 ∣ 3 ^ b` (the divisibility face of the
    above, via the structural `∃ c, 3^b = 2 * c` ↔ `isEven`).
  * `three_pow_inj` — `3 ^ b = 3 ^ d → b = d` (strict monotonicity).
  * `two_three_unique` — the main theorem: cancel the shared `2 ^ a`
    factor (PURE `mul_left_cancel_pos`); any leftover `2`-power would make
    a `3`-power even, contradicting `three_pow_not_even`.

All ∅-axiom.  Parity is run through `PureNat.isEven`; the only
multiplicative cancellation is `NatHelper.mul_left_cancel_pos`.
-/

namespace E213.Meta.Nat.TwoThreeUnique

open E213.Meta.Nat.PureNat (isEven isEven_two_mul pow_add)
open E213.Tactic.NatHelper (mul_left_cancel_pos)

/-! ## §1 — parity of `3`-powers -/

/-- `isEven` of a product with an even left factor: `isEven (2 * k * m) = true`. -/
theorem isEven_two_mul_mul (k m : Nat) : isEven (2 * k * m) = true := by
  rw [PureNat.mul_assoc]; exact isEven_two_mul (k * m)

/-- An odd factor preserves oddness: `isEven n = false → isEven (n * 3) = false`.
    Proved by the `2k+1` representation of an odd number. -/
theorem isEven_mul_three_of_odd {n : Nat} (h : isEven n = false) :
    isEven (n * 3) = false := by
  rcases PureNat.nat_dichotomy n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k would be even, contradicting h
    exact absurd (hk ▸ isEven_two_mul k) (by rw [h]; exact Bool.noConfusion)
  · -- n = 2k+1: n*3 = 2*(3k+1) + 1, odd
    subst hk
    have hrw : (2 * k + 1) * 3 = 2 * (3 * k + 1) + 1 := by
      -- LHS = 2*k*3 + 3 ; RHS = 2*(3*k) + 2 + 1 = 2*k*3 + 3
      rw [PureNat.add_mul, Nat.one_mul]
      rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc, show (2 : Nat) + 1 = 3 from rfl]
      apply congrArg (· + 3)
      rw [PureNat.mul_assoc, Nat.mul_comm k 3, ← PureNat.mul_assoc]
    rw [hrw]; exact PureNat.isEven_two_mul_succ (3 * k + 1)

/-- ★ `3 ^ b` is never even: bare induction on `b`.  The `2`-axis and the
    `3`-axis do not meet. -/
theorem three_pow_not_even : ∀ b, isEven (3 ^ b) = false
  | 0     => rfl
  | b + 1 => by
    rw [Nat.pow_succ]
    exact isEven_mul_three_of_odd (three_pow_not_even b)

/-! ## §2 — `2 ∤ 3 ^ b` (the divisibility face) -/

/-- If `isEven n = true` then `n = 2 * c` for some `c` (structural witness,
    no `propext`). -/
theorem two_dvd_of_isEven {n : Nat} (h : isEven n = true) : ∃ c, n = 2 * c := by
  rcases PureNat.nat_dichotomy n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, hk⟩
  · exact absurd (hk ▸ PureNat.isEven_two_mul_succ k) (by rw [h]; exact Bool.noConfusion)

/-- ★ `2` does not divide `3 ^ b`.  The divisibility statement of
    `three_pow_not_even`, kept as the structural `∃ c, 3^b = 2 * c`. -/
theorem two_not_dvd_three_pow (b : Nat) : ¬ 2 ∣ 3 ^ b := by
  intro h
  obtain ⟨c, hc⟩ := h
  -- 3^b = 2 * c ⇒ isEven (3^b) = true, contradicting three_pow_not_even
  have hev : isEven (3 ^ b) = true := by rw [hc]; exact isEven_two_mul c
  rw [three_pow_not_even b] at hev
  exact Bool.noConfusion hev

/-! ## §3 — injectivity of `3 ^ ·` -/

/-- Strict monotonicity rung: `3 ^ b < 3 ^ (b + 1)`.  Pure: expand
    `3^b * 3 = 3^b + (3^b + 3^b)` and add a positive remainder, avoiding the
    `propext`-tainted core `Nat.mul_lt_mul_left` iff. -/
theorem three_pow_lt_succ (b : Nat) : 3 ^ b < 3 ^ (b + 1) := by
  have hpos : 0 < 3 ^ b := Nat.pos_pow_of_pos b (by decide)
  have hrempos : 0 < 3 ^ b + 3 ^ b := Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)
  have hexp : 3 ^ (b + 1) = 3 ^ b + (3 ^ b + 3 ^ b) := by
    rw [Nat.pow_succ, show (3 : Nat) = 1 + 1 + 1 from rfl]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    rw [Nat.add_assoc]
  rw [hexp]
  exact Nat.lt_add_of_pos_right hrempos

/-- `3 ^ ·` is strictly monotone: `b < e → 3 ^ b < 3 ^ e`. -/
theorem three_pow_strict_mono {b e : Nat} (h : b < e) : 3 ^ b < 3 ^ e := by
  obtain ⟨j, hj⟩ := Nat.le.dest h   -- b + 1 + j = e
  rw [← hj]
  clear hj h e
  induction j with
  | zero => rw [Nat.add_zero]; exact three_pow_lt_succ b
  | succ n ih =>
      rw [show b + 1 + (n + 1) = (b + 1 + n) + 1 from rfl]
      exact Nat.lt_trans ih (three_pow_lt_succ (b + 1 + n))

/-- ★ `3 ^ ·` is injective: `3 ^ b = 3 ^ d → b = d`. -/
theorem three_pow_inj {b d : Nat} (h : 3 ^ b = 3 ^ d) : b = d := by
  rcases Nat.lt_trichotomy b d with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (three_pow_strict_mono hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (three_pow_strict_mono hgt))

/-! ## §4 — main theorem -/

/-- One-sided lemma: when `a ≤ c`, the equation forces `a = c` and `b = d`. -/
theorem two_three_unique_le {a b c d : Nat} (hac : a ≤ c)
    (h : 2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d) : a = c ∧ b = d := by
  obtain ⟨k, hk⟩ := Nat.le.dest hac   -- a + k = c
  -- rewrite 2^c = 2^a * 2^k
  have h2 : 2 ^ a * 3 ^ b = 2 ^ a * (2 ^ k * 3 ^ d) := by
    rw [h, ← hk, pow_add 2 a k, PureNat.mul_assoc]
  have hpos : 0 < 2 ^ a := Nat.pos_pow_of_pos a (by decide)
  -- cancel 2^a
  have hcancel : 3 ^ b = 2 ^ k * 3 ^ d := mul_left_cancel_pos hpos h2
  -- k must be 0, else 3^b is even
  have hk0 : k = 0 := by
    cases k with
    | zero => rfl
    | succ n =>
        exfalso
        -- 2^(n+1) = 2 * 2^n, so 2^(n+1) * 3^d = 2 * (2^n * 3^d) is even
        have heven : isEven (3 ^ b) = true := by
          rw [hcancel, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, PureNat.mul_assoc]
          exact isEven_two_mul (2 ^ n * 3 ^ d)
        rw [three_pow_not_even b] at heven
        exact Bool.noConfusion heven
  -- with k = 0: a = c and 3^b = 3^d
  subst hk0
  have hacEq : a = c := by rw [← hk, Nat.add_zero]
  have hbd : 3 ^ b = 3 ^ d := by
    rw [hcancel, Nat.pow_zero, Nat.one_mul]
  exact ⟨hacEq, three_pow_inj hbd⟩

/-- ★★ **The proven linear floor of the `^`-wall**: the exponent vector of
    a `{2,3}`-power is unique.  No ℕ-linear identity collapses the
    `2`-branch into the `3`-branch. -/
theorem two_three_unique (a b c d : Nat) :
    2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d → a = c ∧ b = d := by
  intro h
  rcases Nat.le_total a c with hac | hca
  · exact two_three_unique_le hac h
  · obtain ⟨hca', hdb⟩ := two_three_unique_le hca h.symm
    exact ⟨hca'.symm, hdb.symm⟩

end E213.Meta.Nat.TwoThreeUnique
