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

/-- **Adding to the right strictly grows** — `a < add a b`, since the additive
    order *is* the add-witness relation (`Raw` has no `0`, so every added element
    is positive).  The additive counterpart of `Divisibility.dvd_mul_right`. -/
theorem lt_add_right (a b : Nat213) : lt a (add a b) := ⟨b, rfl⟩

/-- ★ **Left-monotonicity of addition** — `a < b ⟹ c + a < c + b`, from
    `add_assoc` alone (no order lemma, no `toNat`).  If `add a k = b`, the witness
    is the same `k`: `add (add c a) k = add c (add a k) = add c b`. -/
theorem add_lt_add_left {a b : Nat213} (h : lt a b) (c : Nat213) :
    lt (add c a) (add c b) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [add_assoc, hk]⟩

/-- ★ **Right-monotonicity of addition** — `a < b ⟹ a + c < b + c` (via `add_comm`). -/
theorem add_lt_add_right {a b : Nat213} (h : lt a b) (c : Nat213) :
    lt (add a c) (add b c) := by
  rw [add_comm a c, add_comm b c]; exact add_lt_add_left h c

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

/-- `a < succ a` — the successor strictly exceeds (witness `one`, `add_one_right`). -/
theorem lt_succ_self (a : Nat213) : lt a (succ a) := ⟨one, add_one_right a⟩

/-- `succ a < succ b ⟹ a < b` — the successor reflects strict order (trichotomy +
    `succ_lt_succ_of_lt`). -/
theorem lt_of_succ_lt_succ {a b : Nat213} (h : lt (succ a) (succ b)) : lt a b := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ h) (lt_irrefl (succ b))
  · exact absurd (lt_trans h (succ_lt_succ_of_lt h1)) (lt_irrefl (succ a))

/-! ## The non-strict order `le`

`le a b := a = b ∨ lt a b`, the reflexive closure of the native strict order.
A genuine **partial order** (refl, trans, antisymm) that is also **total** — the
non-strict twin of `lt_strict_total_order`, on the distinguishing's own counting
object, with no Lean `Nat` order and no `toNat`. -/

/-- Non-strict order: `a ≤ b` iff `a = b` or `a < b`. -/
def le (a b : Nat213) : Prop := a = b ∨ lt a b

/-- Reflexivity. -/
theorem le_refl (a : Nat213) : le a a := Or.inl rfl

/-- A strict inequality is a non-strict one. -/
theorem le_of_lt {a b : Nat213} (h : lt a b) : le a b := Or.inr h

/-- `a ≤ b ⟹ a ≤ succ b` — the successor step. -/
theorem le_succ_of_le {a b : Nat213} (h : le a b) : le a (succ b) := by
  rcases h with rfl | h
  · exact Or.inr (lt_succ_self a)
  · exact Or.inr (lt_trans h (lt_succ_self b))

/-- ★ **Transitivity** of `≤` — splits on each disjunct, composing with `lt_trans`. -/
theorem le_trans {a b c : Nat213} (hab : le a b) (hbc : le b c) : le a c := by
  rcases hab with rfl | hab
  · exact hbc
  · rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (lt_trans hab hbc)

/-- ★ **Antisymmetry** of `≤` — `a ≤ b → b ≤ a → a = b`.  A two-way strict
    inequality contradicts `lt_asymm`. -/
theorem le_antisymm {a b : Nat213} (hab : le a b) (hba : le b a) : a = b := by
  rcases hab with rfl | hab
  · rfl
  · rcases hba with hba | hba
    · exact hba.symm
    · exact absurd hba (lt_asymm hab)

/-- ★ **Totality** of `≤` — every pair is comparable (from trichotomy). -/
theorem le_total (a b : Nat213) : le a b ∨ le b a := by
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- ★★★ **`le` is a total partial order on the Raw-generated ℕ₊** — reflexive,
    transitive, antisymmetric, total.  The non-strict twin of
    `lt_strict_total_order`; entirely over `Nat213` (no `toNat`, no Lean `Nat`
    order lemma). -/
theorem le_total_order :
    (∀ a : Nat213, le a a)
    ∧ (∀ a b c : Nat213, le a b → le b c → le a c)
    ∧ (∀ a b : Nat213, le a b → le b a → a = b)
    ∧ (∀ a b : Nat213, le a b ∨ le b a) :=
  ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩

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

/-- ★ **Strict monotonicity of right multiplication** — `a < b ⟹ a·c < b·c` (via `mul_comm`
    + `lt_mul_left`). -/
theorem lt_mul_right {a b c : Nat213} (h : lt a b) : lt (mul a c) (mul b c) := by
  rw [mul_comm a c, mul_comm b c]; exact lt_mul_left h

/-- ★★ **Strict monotonicity of exponentiation in the base** — `a < b ⟹ a^n < b^n` for every
    exponent `n`.  Induction on `n`: the step chains `a·a^n < a·b^n < b·b^n`
    (`lt_mul_left` on the IH, then `lt_mul_right` on the base).  No `toNat`. -/
theorem pow_lt_pow_base {a b : Nat213} (h : lt a b) (n : Nat213) : lt (pow a n) (pow b n) := by
  induction n with
  | one => rw [pow_one, pow_one]; exact h
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact lt_trans (lt_mul_left ih) (lt_mul_right h)

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
