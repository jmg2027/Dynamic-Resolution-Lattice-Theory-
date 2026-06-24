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

/-- Irreflexivity — via the **native** `Peano.add_ne_self` (no `toNat`). -/
theorem lt_irrefl (a : Nat213) : ¬ lt a a := fun ⟨c, hc⟩ => add_ne_self a c hc

/-- A strict inequality is a disequality. -/
theorem lt_ne {a b : Nat213} (h : lt a b) : a ≠ b := fun he => lt_irrefl b (he ▸ h)

/-- ★ **Transitivity** — `a < b → b < c → a < c`.  Compose the add-witnesses
    (`add a c₁ = b`, `add b c₂ = c`) into `add c₁ c₂` via `add_assoc`; no order
    lemma, no `toNat`.  The native strict order is genuinely transitive. -/
theorem lt_trans {a b c : Nat213} (h1 : lt a b) (h2 : lt b c) : lt a c := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  exact ⟨add x y, by rw [← add_assoc, hx, hy]⟩

/-- ★ **Asymmetry** — `a < b ⟹ ¬ b < a`.  Transitivity would give `a < a`,
    contradicting irreflexivity. -/
theorem lt_asymm {a b : Nat213} (h : lt a b) : ¬ lt b a :=
  fun h' => lt_irrefl a (lt_trans h h')

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

/-- ★★★ **Strict monotonicity of left multiplication** — `b < c ⟹ a·b < a·c`,
    derived purely from left-distributivity (`mul_add`); no order lemma, no
    `toNat`.  If `add b k = c`, the witness is `mul a k`:
    `a·c = a·(b+k) = a·b + a·k`. -/
theorem lt_mul_left {a b c : Nat213} (h : lt b c) : lt (mul a b) (mul a c) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨mul a k, by rw [← hk, mul_add]⟩

/-- ★★★ **Left cancellation, native** — `a·b = a·c ⟹ b = c`.  By trichotomy +
    strict monotonicity (`lt_mul_left`) + `lt_ne`; mirrors `mul_self_inj`.  This
    replaces the previous `toNat`-laundered cancellation: the divisibility
    partial order's antisymmetry (`Divisibility.dvd_antisymm`) now stands on
    `Nat213` all the way down — zero `toNat`, zero Lean-`Nat` lemmas in its
    dependency cone.  See the `the_descent_leg` frontier
    (the toNat-cone bet). -/
theorem mul_left_cancel {a b c : Nat213} (h : mul a b = mul a c) : b = c := by
  rcases lt_trichotomy b c with hlt | heq | hgt
  · exact absurd h (lt_ne (lt_mul_left hlt))
  · exact heq
  · exact absurd h.symm (lt_ne (lt_mul_left hgt))

/-- ★ **Right cancellation, native** — `a·c = b·c ⟹ a = b` (via `mul_comm`). -/
theorem mul_right_cancel {a b c : Nat213} (h : mul a c = mul b c) : a = b := by
  apply mul_left_cancel (a := c)
  rw [mul_comm c a, mul_comm c b]
  exact h

/-- ★★★ **`lt` is a strict total order on the Raw-generated ℕ₊** — irreflexive,
    transitive, and trichotomous (every pair is comparable).  The additive order
    on the distinguishing's own counting object, established with **no Lean `Nat`
    order lemma and no `toNat`** — entirely from `add`'s structure (cf.
    `Divisibility.divisibility_preorder_with_bottom`, the multiplicative twin). -/
theorem lt_strict_total_order :
    (∀ a : Nat213, ¬ lt a a)
    ∧ (∀ a b c : Nat213, lt a b → lt b c → lt a c)
    ∧ (∀ a b : Nat213, lt a b ∨ a = b ∨ lt b a) :=
  ⟨lt_irrefl, fun _ _ _ => lt_trans, lt_trichotomy⟩

end E213.Lens.Number.Nat213.Order
