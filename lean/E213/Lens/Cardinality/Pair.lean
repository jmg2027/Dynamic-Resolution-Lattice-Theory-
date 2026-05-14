import E213.Prelude
import E213.Meta.Tactic.NatHelper
open E213.Tactic.NatHelper

/-!
# Infinity.Pair: injective pairing `ℕ × ℕ → ℕ`

Defines `pair x y := 2^(x+y) + y` and proves it is injective.
The key arithmetic fact is `Nat.lt_two_pow_self` (core Lean):
`n < 2^n` for every `n`.  This lets the next "sum class"
dominate any residual tail.

This is the pairing we use in `Infinity.Godel` to encode
`Tree → ℕ` injectively (Σ2).
-/

namespace E213.Lens.Cardinality

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
  have hy : y < 2^(x + y) := Nat.lt_of_le_of_lt h1 h2
  have hsum : 2^(x + y) + y < 2^(x + y) + 2^(x + y) :=
    Nat.add_lt_add_left hy _
  have hpow : 2^(x + y) + 2^(x + y) = 2^(x + y + 1) := by
    show 2^(x + y) + 2^(x + y) = 2^(x + y) * 2
    exact (Nat.mul_two _).symm
  exact hpow ▸ hsum

/-- `2^(x+y) ≤ pair x y`: the value is at least the
    leading power-of-2 term. -/
theorem pow_le_pair (x y : Nat) :
    2^(x + y) ≤ pair x y :=
  Nat.le_add_right _ _

end E213.Lens.Cardinality

namespace E213.Lens.Cardinality

/-- **Pair injectivity — 4-arg form.**  If `pair x₁ y₁ =
    pair x₂ y₂` then `x₁ = x₂ ∧ y₁ = y₂`.  Proof via
    trichotomy on `x₁+y₁` vs `x₂+y₂` using the
    previous-pow/next-pow bounds. -/
theorem pair_injective_4 :
    ∀ x1 y1 x2 y2, pair x1 y1 = pair x2 y2 → x1 = x2 ∧ y1 = y2 := by
  intro x1 y1 x2 y2 heq
  match Nat.lt_trichotomy (x1 + y1) (x2 + y2) with
  | Or.inl hlt =>
    exfalso
    have h1 : pair x1 y1 < 2^(x1 + y1 + 1) := pair_lt_next_pow x1 y1
    have h2 : 2^(x1 + y1 + 1) ≤ 2^(x2 + y2) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hlt)
    have h3 : 2^(x2 + y2) ≤ pair x2 y2 := pow_le_pair x2 y2
    have hchain : pair x1 y1 < pair x2 y2 :=
      Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)
    exact Nat.lt_irrefl _ (heq ▸ hchain)
  | Or.inr (Or.inl heqs) =>
    have hex : 2^(x1 + y1) + y1 = 2^(x2 + y2) + y2 := heq
    have heq' : 2^(x2 + y2) + y1 = 2^(x2 + y2) + y2 := heqs ▸ hex
    have hy : y1 = y2 := add_left_cancel heq'
    have hx_eq : x1 + y2 = x2 + y2 := hy ▸ heqs
    have hx : x1 = x2 := add_right_cancel hx_eq
    exact ⟨hx, hy⟩
  | Or.inr (Or.inr hgt) =>
    exfalso
    have h1 : pair x2 y2 < 2^(x2 + y2 + 1) := pair_lt_next_pow x2 y2
    have h2 : 2^(x2 + y2 + 1) ≤ 2^(x1 + y1) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hgt)
    have h3 : 2^(x1 + y1) ≤ pair x1 y1 := pow_le_pair x1 y1
    have hchain : pair x2 y2 < pair x1 y1 :=
      Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)
    exact Nat.lt_irrefl _ (heq.symm ▸ hchain)

/-- `pair` as a function on `Nat × Nat` is injective. -/
theorem pair_injective :
    Function.Injective (fun p : Nat × Nat => pair p.1 p.2) := by
  intro ⟨x1, y1⟩ ⟨x2, y2⟩ heq
  have ⟨hx, hy⟩ := pair_injective_4 x1 y1 x2 y2 heq
  exact congr (congrArg Prod.mk hx) hy

end E213.Lens.Cardinality
