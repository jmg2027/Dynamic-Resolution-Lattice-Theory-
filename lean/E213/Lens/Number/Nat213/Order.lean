import E213.Lens.Number.Nat213.Peano

/-!
# Lens.Number.Nat213.Order — native strict order and square-injectivity

`Nat213` order, built **without Lean `Nat` order** (core `Nat.lt_or_ge`, `Nat.le_antisymm`,
`Nat.mul_lt_mul_right` all pull `propext` / `Classical.choice` / `Quot.sound`).  The order
is the add-witness relation: `a < b` iff `b` is reached from `a` by adding a `Nat213`.
Because `Nat213` has no `0`, every added element is positive, so this is a genuine strict
order, and strict monotonicity of multiplication and of squaring fall out *algebraically*
— from distributivity, with no order lemmas at all.

The payoff is **square-injectivity** `a·a = b·b → a = b` (`mul_self_inj`), the fact the
multiplicative completion (`ℚ_+`, `NatPairToQPos`) needs to characterise its reciprocal
fixed points exactly — the multiplicative twin of `ℤ`'s `zero_unique_negation_fixed`.

All theorems ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.Order

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213

/-- Strict order: `a < b` iff `b` is `a` with a positive `Nat213` added. -/
def lt (a b : Nat213) : Prop := ∃ c, add a c = b

/-- `add a c ≠ a` — adding any `Nat213` strictly grows (there is no additive `0`). -/
theorem add_ne_self (a c : Nat213) : add a c ≠ a := by
  intro h
  have hn : (add a c).toNat = a.toNat := congrArg toNat h
  rw [toNat_add] at hn
  have h0 : a.toNat + c.toNat = a.toNat + 0 := hn
  have hc0 : c.toNat = 0 := E213.Tactic.NatHelper.add_left_cancel h0
  have hge : c.toNat ≥ 1 := toNat_ge_one c
  rw [hc0] at hge
  exact absurd hge (by decide)

/-- Irreflexivity. -/
theorem lt_irrefl (a : Nat213) : ¬ lt a a := fun ⟨c, hc⟩ => add_ne_self a c hc

/-- A strict inequality is a disequality. -/
theorem lt_ne {a b : Nat213} (h : lt a b) : a ≠ b := fun he => lt_irrefl b (he ▸ h)

/-- `a < b ⟹ succ a < succ b` (the successor is order-preserving). -/
theorem succ_lt_succ_of_lt {a b : Nat213} (h : lt a b) : lt (succ a) (succ b) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by show succ (add a c) = succ b; rw [hc]⟩

/-- ★ **Trichotomy**: for all `a b`, exactly one of `a < b`, `a = b`, `b < a` holds
    (here: at least one — the disjunction).  Structural double recursion. -/
theorem lt_trichotomy : ∀ a b : Nat213, lt a b ∨ a = b ∨ lt b a
  | one,    one    => Or.inr (Or.inl rfl)
  | one,    succ b => Or.inl ⟨b, rfl⟩
  | succ a, one    => Or.inr (Or.inr ⟨a, rfl⟩)
  | succ a, succ b => by
      rcases lt_trichotomy a b with h | h | h
      · exact Or.inl (succ_lt_succ_of_lt h)
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr (succ_lt_succ_of_lt h))

/-- ★★★ **Strict monotonicity of squaring** — `a < b ⟹ a·a < b·b`, derived purely from
    distributivity (`add_mul`, `mul_add`, `add_assoc`); no order lemma is used.  If
    `add a k = b`, then `b·b = a·a + (a·k + (k·a + k·k))`, exhibiting the witness. -/
theorem lt_mul_self {a b : Nat213} (h : lt a b) : lt (mul a a) (mul b b) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨add (mul a k) (add (mul k a) (mul k k)), ?_⟩
  rw [← hk, add_mul a k (add a k), mul_add a a k, mul_add k a k, add_assoc]

/-- ★★★ **Square-injectivity** — `a·a = b·b ⟹ a = b`.  By trichotomy: a strict
    inequality either way gives a strict inequality of squares (`lt_mul_self`), which
    contradicts the equality (`lt_ne`); the remaining case is `a = b`.  This is the
    multiplicative analogue of `ℤ`'s constructor-analysis uniqueness — the fact
    `ℚ_+`'s reciprocal fixed-point characterisation needs. -/
theorem mul_self_inj {a b : Nat213} (h : mul a a = mul b b) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (lt_ne (lt_mul_self hlt))
  · exact heq
  · exact absurd h.symm (lt_ne (lt_mul_self hgt))

end E213.Lens.Number.Nat213.Order
