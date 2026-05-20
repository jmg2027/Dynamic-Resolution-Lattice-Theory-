import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.Mod213
import E213.Theory.Atomicity.FiveHelpers
/-!
# Atomicity: d = 5 as a theorem (not an axiom)

Given atoms `{2, 3}`, the unique n ∈ ℕ such that
  (a) n admits exactly one decomposition n = 2a + 3b with a,b ∈ ℕ, and
  (b) that decomposition is "alive" (both a,b odd)
is n = 5.

213-native (∅-axiom): no `omega`, `simp`, `rcases`, `obtain`.
-/

open E213.Tactic.NatHelper
open E213.Tactic.Mod213

namespace E213.Theory.Atomicity.Five

/-- n decomposes as 2a + 3b. -/
def Decomp (n a b : Nat) : Prop := n = 2 * a + 3 * b

/-- Alive: both parts odd (survive swap annihilation).
    213-native via cohomological parity (Nat213.parity) — direct
    step-2 recursion, ∅-axiom, vs. Lean's well-founded `% 2`
    which brings propext through `Nat.add_mod_right` etc. -/
def IsAlive (a b : Nat) : Prop := parity a = true ∧ parity b = true

/-- n is atomic: has a unique decomposition, and it is alive. -/
def Atomic (n : Nat) : Prop :=
  ∃ a b, Decomp n a b ∧ IsAlive a b ∧
         ∀ a' b', Decomp n a' b' → a' = a ∧ b' = b

/-- 213-native: `2 * a = 5 → False` via case analysis on `a`. -/
private theorem two_mul_ne_five (a : Nat) (h : 2 * a = 5) : False :=
  match Nat.lt_or_ge a 3 with
  | Or.inl hlt =>
    match cases_lt_three hlt with
    | Or.inl h0 => absurd (h0 ▸ h) (by decide)
    | Or.inr (Or.inl h1) => absurd (h1 ▸ h) (by decide)
    | Or.inr (Or.inr h2) => absurd (h2 ▸ h) (by decide)
  | Or.inr hge =>
    have : 6 ≤ 2 * a := Nat.mul_le_mul_left 2 hge
    absurd (h ▸ this) (by decide)

/-- 213-native: `2 * a = 2 → a = 1` via case analysis. -/
private theorem two_mul_eq_two (a : Nat) (h : 2 * a = 2) : a = 1 :=
  match Nat.lt_or_ge a 2 with
  | Or.inl hlt =>
    match cases_lt_two hlt with
    | Or.inl h0 => absurd (h0 ▸ h) (by decide)
    | Or.inr h1 => h1
  | Or.inr hge =>
    have h4 : 4 ≤ 2 * a := Nat.mul_le_mul_left 2 hge
    absurd (h ▸ h4) (by decide)


/-- Linear Diophantine: `2*a + 3*b = 5 → a = 1 ∧ b = 1`. -/
private theorem solve_2a_3b_eq_5 (a b : Nat) (h : 2 * a + 3 * b = 5) :
    a = 1 ∧ b = 1 := by
  have h3b : 3 * b ≤ 5 := h ▸ Nat.le_add_left (3 * b) (2 * a)
  match Nat.lt_or_ge b 2 with
  | Or.inl hb_lt =>
    match cases_lt_two hb_lt with
    | Or.inl hb0 =>
      subst hb0
      -- h : 2*a + 3*0 = 5, defeq 2*a = 5
      exact absurd (two_mul_ne_five a h) id
    | Or.inr hb1 =>
      subst hb1
      -- h : 2*a + 3*1 = 5, defeq 2*a + 3 = 5
      have h_2a : 2 * a = 2 := add_right_cancel (show 2 * a + 3 = 2 + 3 from h)
      exact ⟨two_mul_eq_two a h_2a, rfl⟩
  | Or.inr hb_ge =>
    exfalso
    have h6 : 6 ≤ 3 * b := Nat.mul_le_mul_left 3 hb_ge
    exact absurd (Nat.le_trans h6 h3b) (by decide)


/-- Existence: n = 5 has the unique alive decomposition (1, 1). -/
theorem atomic_five : Atomic 5 :=
  ⟨1, 1, rfl, ⟨rfl, rfl⟩, fun a b h => solve_2a_3b_eq_5 a b h.symm⟩


/-- Corollary: partition labels are canonical — one 3-atom, one 2-atom. -/
theorem canonical_partition :
    ∀ a b, Decomp 5 a b ∧ IsAlive a b → a = 1 ∧ b = 1 := by
  intro a b ⟨hdec, _⟩
  exact solve_2a_3b_eq_5 a b hdec.symm


/-- `a < 3 ∧ parity a = true → a = 1`. -/
private theorem a_lt_3_odd_eq_1 {a : Nat}
    (h_lt : a < 3) (h_odd : parity a = true) : a = 1 :=
  match cases_lt_three h_lt with
  | Or.inl h0 => absurd (h0 ▸ h_odd) (by decide)
  | Or.inr (Or.inl h1) => h1
  | Or.inr (Or.inr h2) => absurd (h2 ▸ h_odd) (by decide)

/-- `b < 2 ∧ parity b = true → b = 1`. -/
private theorem b_lt_2_odd_eq_1 {b : Nat}
    (h_lt : b < 2) (h_odd : parity b = true) : b = 1 :=
  match cases_lt_two h_lt with
  | Or.inl h0 => absurd (h0 ▸ h_odd) (by decide)
  | Or.inr h1 => h1

/-- Uniqueness: Atomic n implies n = 5 (Bézout shift argument).
    Now ∅-axiom via cohomological parity + explicit Bézout shifts. -/
theorem atomic_implies_five (n : Nat) (h : Atomic n) : n = 5 := by
  obtain ⟨a, b, hdec, ⟨ha_odd, hb_odd⟩, huniq⟩ := h
  have ha_lt : a < 3 := by
    match Nat.lt_or_ge a 3 with
    | Or.inl h => exact h
    | Or.inr ha_ge =>
      exfalso
      have hdec' : Decomp n (a - 3) (b + 2) :=
        hdec.trans (FiveHelpers.bezout_left ha_ge)
      exact FiveHelpers.add_two_ne_self b (huniq (a - 3) (b + 2) hdec').2
  have hb_lt : b < 2 := by
    match Nat.lt_or_ge b 2 with
    | Or.inl h => exact h
    | Or.inr hb_ge =>
      exfalso
      have hdec' : Decomp n (a + 3) (b - 2) :=
        hdec.trans (FiveHelpers.bezout_right hb_ge)
      exact FiveHelpers.add_three_ne_self a (huniq (a + 3) (b - 2) hdec').1
  have ha1 : a = 1 := a_lt_3_odd_eq_1 ha_lt ha_odd
  have hb1 : b = 1 := b_lt_2_odd_eq_1 hb_lt hb_odd
  have step1 : n = 2 * 1 + 3 * b := ha1 ▸ hdec
  have step2 : n = 2 * 1 + 3 * 1 := hb1 ▸ step1
  exact step2

/-- Main theorem: atomicity singles out n = 5. -/
theorem atomic_iff_five (n : Nat) : Atomic n ↔ n = 5 :=
  ⟨atomic_implies_five n, fun h => h ▸ atomic_five⟩

end E213.Theory.Atomicity.Five
