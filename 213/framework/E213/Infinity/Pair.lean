import E213.Prelude

/-!
# Infinity.Pair: injective pairing `ℕ × ℕ → ℕ`

Defines `pair x y := 2^(x+y) + y` and proves it is injective.
The key arithmetic fact is `Nat.lt_two_pow_self` (core Lean):
`n < 2^n` for every `n`.  This lets the next "sum class"
dominate any residual tail.

This is the pairing we use in `Infinity.Godel` to encode
`Tree → ℕ` injectively (Σ2).
-/

namespace E213.Infinity

/-- Pairing: `pair x y = 2^(x+y) + y`.  Not a bijection
    (many `ℕ` are skipped) but injective, which is all we
    need for Σ2. -/
def pair (x y : Nat) : Nat := 2^(x + y) + y

/-- `pair x y < 2^(x+y+1)`: the value stays below the next
    power of 2, because `y ≤ x + y < 2^(x+y)` by
    `Nat.lt_two_pow_self`. -/
theorem pair_lt_next_pow (x y : Nat) :
    pair x y < 2^(x + y + 1) := by
  show 2^(x + y) + y < 2^(x + y + 1)
  have h1 : y ≤ x + y := Nat.le_add_left y x
  have h2 : x + y < 2^(x + y) := Nat.lt_two_pow_self
  have h3 : 2^(x + y + 1) = 2 * 2^(x + y) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  omega

/-- `2^(x+y) ≤ pair x y`: the value is at least the
    leading power-of-2 term. -/
theorem pow_le_pair (x y : Nat) :
    2^(x + y) ≤ pair x y := by
  show 2^(x + y) ≤ 2^(x + y) + y
  omega

end E213.Infinity

namespace E213.Infinity

/-- **Pair injectivity — 4-arg form.**  If `pair x₁ y₁ =
    pair x₂ y₂` then `x₁ = x₂ ∧ y₁ = y₂`.  Proof via
    trichotomy on `x₁+y₁` vs `x₂+y₂` using the
    previous-pow/next-pow bounds. -/
theorem pair_injective_4 :
    ∀ x1 y1 x2 y2, pair x1 y1 = pair x2 y2 → x1 = x2 ∧ y1 = y2 := by
  intro x1 y1 x2 y2 heq
  rcases Nat.lt_trichotomy (x1 + y1) (x2 + y2) with hlt | heqs | hgt
  · exfalso
    have h1 : pair x1 y1 < 2^(x1 + y1 + 1) := pair_lt_next_pow x1 y1
    have h2 : 2^(x1 + y1 + 1) ≤ 2^(x2 + y2) := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      omega
    have h3 : 2^(x2 + y2) ≤ pair x2 y2 := pow_le_pair x2 y2
    omega
  · have hy : y1 = y2 := by
      have : 2^(x1 + y1) + y1 = 2^(x2 + y2) + y2 := heq
      rw [heqs] at this; omega
    have hx : x1 = x2 := by omega
    exact ⟨hx, hy⟩
  · exfalso
    have h1 : pair x2 y2 < 2^(x2 + y2 + 1) := pair_lt_next_pow x2 y2
    have h2 : 2^(x2 + y2 + 1) ≤ 2^(x1 + y1) := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      omega
    have h3 : 2^(x1 + y1) ≤ pair x1 y1 := pow_le_pair x1 y1
    omega

/-- `pair` as a function on `Nat × Nat` is injective. -/
theorem pair_injective :
    Function.Injective (fun p : Nat × Nat => pair p.1 p.2) := by
  intro ⟨x1, y1⟩ ⟨x2, y2⟩ heq
  obtain ⟨hx, hy⟩ := pair_injective_4 x1 y1 x2 y2 heq
  exact Prod.mk.injEq .. |>.mpr ⟨hx, hy⟩

end E213.Infinity
