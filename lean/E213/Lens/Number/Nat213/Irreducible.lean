import E213.Lens.Number.Nat213.Divisibility

/-!
# Lens.Number.Nat213.Irreducible — irreducibility over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, leg-2 *depth* (the `the_descent_leg` frontier M1).  Divisibility
(`Divisibility.lean`) gave a partial-order discipline over `Nat213` (the distinguishing's own counting
object).  This file takes the next rung: **irreducibility** — `2`, `3`, `5` are irreducible, `4` is
not — defined and proved entirely over `Nat213` with its own `mul`, no detour through Lean `Nat`.

It stands on the now-`toNat`-free foundation (the divisibility cone was de-laundered, the descent-leg
"toNat-cone bet"): the cancellation it uses (`mul_left_cancel`) is `Order`'s native version, and the
small-number reasoning is built from a native `lt_succ_iff` enumeration + a native cofactor bound, so
the whole cone here is `toNat`-free too.  This is the first irreducibility ever stated over the
Raw-generated carrier, and rung 1 of the Fundamental-Theorem-of-Arithmetic capstone (M1→M6).

`5` irreducible is genuine elementary number theory (its proper divisors are enumerated and none but
`one` divides) — not a relabeling: the content is forced by `Nat213`'s own multiplication.  ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.Irreducible

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul add one succ two three four five mul_one one_mul mul_comm mul_add
   add_one_right add_succ_right succ_ne_one)
open E213.Lens.Number.Nat213.Order (lt mul_left_cancel)
open E213.Lens.Number.Nat213.Divisibility (Dvd dvd_imp_eq_or_lt)

/-! ## Native small-order infrastructure (no `toNat`) -/

/-- `add a c ≠ one` — every sum is a successor (no additive bottom below `one`). -/
theorem add_ne_one : ∀ (a c : Nat213), add a c ≠ one
  | one,    c => fun h => succ_ne_one c h
  | succ m, c => fun h => succ_ne_one (add m c) h

/-- Nothing is strictly below `one`. -/
theorem not_lt_one (a : Nat213) : ¬ lt a one := fun ⟨c, hc⟩ => add_ne_one a c hc

/-- `lt one a` for any non-unit `a` (a non-`one` is a successor, hence `≥ 2 > 1`). -/
theorem lt_one_of_ne_one {a : Nat213} (h : a ≠ one) : lt one a := by
  cases a with
  | one => exact absurd rfl h
  | succ a' => exact ⟨a', rfl⟩

/-- ★ `a < succ b ↔ a = b ∨ a < b` — the native enumeration step. -/
theorem lt_succ_iff {a b : Nat213} : lt a (succ b) ↔ (a = b ∨ lt a b) := by
  constructor
  · rintro ⟨c, hc⟩
    cases c with
    | one => exact Or.inl (Nat213.succ.inj (add_one_right a ▸ hc))
    | succ c' => exact Or.inr ⟨c', Nat213.succ.inj (add_succ_right a c' ▸ hc)⟩
  · rintro (rfl | ⟨c, hc⟩)
    · exact ⟨one, add_one_right a⟩
    · exact ⟨succ c, by rw [add_succ_right, hc]⟩

/-- `a < 2 ⟹ a = 1`. -/
theorem lt_two_cases {a : Nat213} (h : lt a two) : a = one := by
  rcases lt_succ_iff.mp h with h1 | h0
  · exact h1
  · exact absurd h0 (not_lt_one a)

/-- `a < 3 ⟹ a ∈ {1,2}`. -/
theorem lt_three_cases {a : Nat213} (h : lt a three) : a = one ∨ a = two := by
  rcases lt_succ_iff.mp h with h2 | h
  · exact Or.inr h2
  · exact Or.inl (lt_two_cases h)

/-- `a < 5 ⟹ a ∈ {1,2,3,4}`. -/
theorem lt_five_cases {a : Nat213} (h : lt a five) :
    a = one ∨ a = two ∨ a = three ∨ a = four := by
  rcases lt_succ_iff.mp h with h4 | h
  · exact Or.inr (Or.inr (Or.inr h4))
  rcases lt_succ_iff.mp h with h3 | h
  · exact Or.inr (Or.inr (Or.inl h3))
  rcases lt_succ_iff.mp h with h2 | h
  · exact Or.inr (Or.inl h2)
  rcases lt_succ_iff.mp h with h1 | h
  · exact Or.inl h1
  exact absurd h (not_lt_one a)

/-- A non-unit factor strictly grows the product: `1 < b ⟹ a < a·b`
    (from `a·b = a·(1+c) = a + a·c`, native, no order lemma). -/
theorem lt_left_mul {a b : Nat213} (hb : lt one b) : lt a (mul a b) := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨mul a c, by rw [← hc, mul_add, mul_one]⟩

/-- Symmetric: `1 < a ⟹ b < a·b`. -/
theorem lt_right_mul {a b : Nat213} (ha : lt one a) : lt b (mul a b) := by
  rw [mul_comm]; exact lt_left_mul ha

/-- **Cofactor bound**: a non-unit factor's cofactor is strictly smaller than the product —
    `a ≠ 1 ∧ p = a·c ⟹ c < p`.  This is what makes the proper-divisor search finite. -/
theorem cofactor_lt {a c p : Nat213} (ha : a ≠ one) (h : p = mul a c) : lt c p := by
  have hlt : lt c (mul a c) := lt_right_mul (lt_one_of_ne_one ha)
  rw [← h] at hlt
  exact hlt

/-! ## Irreducibility -/

/-- A unit over `Nat213` is exactly `one` (`mul x y = one → x = one`, `Divisibility.mul_eq_one`). -/
def IsUnit (a : Nat213) : Prop := a = one

/-- **Irreducible over the Raw-generated ℕ₊**: not a unit, and every factorization has a unit factor.
    Stated with `Nat213`'s own `mul`; no Lean `Nat`. -/
def Irreducible (p : Nat213) : Prop :=
  p ≠ one ∧ ∀ a b : Nat213, p = mul a b → a = one ∨ b = one

/-- The convenient characterization: `p` irreducible iff `p ≠ 1` and its only divisors are `1` and
    `p`.  (The `⟸` direction; the cancellation closes the cofactor leg.) -/
theorem irreducible_of_only_trivial_divisors {p : Nat213}
    (hp : p ≠ one) (hdiv : ∀ a : Nat213, Dvd a p → a = one ∨ a = p) : Irreducible p := by
  refine ⟨hp, ?_⟩
  intro a b hab
  rcases hdiv a ⟨b, hab⟩ with ha | hap
  · exact Or.inl ha
  · refine Or.inr ?_
    have e1 : mul a b = a := by rw [← hab, hap]
    have e2 : mul a b = mul a one := by rw [e1, mul_one]
    exact mul_left_cancel e2

/-- `2` is irreducible: its only proper divisor candidate (`< 2`) is `1`. -/
theorem two_irreducible : Irreducible two := by
  refine irreducible_of_only_trivial_divisors (by decide) ?_
  rintro a ⟨c, hc⟩
  rcases dvd_imp_eq_or_lt ⟨c, hc⟩ with rfl | hlt
  · exact Or.inr rfl
  · exact Or.inl (lt_two_cases hlt)

/-- `3` is irreducible: the only proper divisor below `3` that could divide is `1`
    (`2 ∤ 3` — the cofactor search refutes `3 = 2·c`). -/
theorem three_irreducible : Irreducible three := by
  refine irreducible_of_only_trivial_divisors (by decide) ?_
  rintro a ⟨c, hc⟩
  rcases dvd_imp_eq_or_lt ⟨c, hc⟩ with rfl | hlt
  · exact Or.inr rfl
  · rcases lt_three_cases hlt with rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hcf : lt c three := cofactor_lt (by decide) hc
      rcases lt_three_cases hcf with rfl | rfl <;> exact absurd hc (by decide)

/-- ★ `5` is irreducible — genuine elementary number theory over `Nat213`: every proper divisor
    is enumerated (`< 5 ⟹ ∈ {1,2,3,4}`), the cofactor is bounded `< 5`, and no `(a,c)` with both
    `< 5` has `a·c = 5` except via the unit `1`.  The content is forced by `Nat213`'s own `mul`. -/
theorem five_irreducible : Irreducible five := by
  refine irreducible_of_only_trivial_divisors (by decide) ?_
  rintro a ⟨c, hc⟩
  rcases dvd_imp_eq_or_lt ⟨c, hc⟩ with rfl | hlt
  · exact Or.inr rfl
  · rcases lt_five_cases hlt with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    all_goals (
      exfalso
      have hcf : lt c five := cofactor_lt (by decide) hc
      rcases lt_five_cases hcf with rfl | rfl | rfl | rfl <;> exact absurd hc (by decide))

/-- `4` is **not** irreducible: `4 = 2·2` with neither factor a unit. -/
theorem four_not_irreducible : ¬ Irreducible four := by
  rintro ⟨_, h⟩
  rcases h two two (by decide) with h1 | h1 <;> exact absurd h1 (by decide)

/-- **An irreducible's only divisors are `1` and itself** — the structural payoff, over `Nat213`. -/
theorem irreducible_divisors {p a : Nat213} (hp : Irreducible p) (h : Dvd a p) :
    a = one ∨ a = p := by
  obtain ⟨c, hc⟩ := h
  rcases hp.2 a c hc with ha | hc1
  · exact Or.inl ha
  · refine Or.inr ?_
    rw [hc, hc1, mul_one]

end E213.Lens.Number.Nat213.Irreducible
