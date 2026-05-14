import E213.Meta.Tactic.NatHelper
/-!
# Non-decomposable integers: {2, 3}

Proposition (per archival PAPER1 §6.5, deleted 2026-05-12):
  an integer `n ≥ 2` cannot be expressed
as a sum `n = n_1 + … + n_k` with `k ≥ 2` and each `n_i ≥ 2` iff
`n ∈ {2, 3}`.

Any `k`-part decomposition collapses to a 2-part one — so we use
the 2-part form below.

213-native (∅-axiom): no `omega`, `simp`, `rcases`, or `simpa`.
-/

open E213.Tactic.NatHelper

namespace E213.Theory.Atomicity.NonDecomposable

/-- Expressible as `a + b` with `a, b ≥ 2`. -/
def Decomposable (n : Nat) : Prop :=
  ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = n

/-- Non-decomposable and `≥ 2` (the "atoms"). -/
def NonDecomposable (n : Nat) : Prop :=
  n ≥ 2 ∧ ¬ Decomposable n

private theorem two_or_three_of_lt_four {n : Nat}
    (h2 : 2 ≤ n) (h4 : n < 4) : n = 2 ∨ n = 3 :=
  match Nat.lt_or_ge n 3 with
  | Or.inl hlt3 =>
    Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hlt3) h2)
  | Or.inr hge3 =>
    Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h4) hge3)

private theorem n_sub_two_ge_two_of_ge_four {n : Nat} (h : 4 ≤ n) : 2 ≤ n - 2 :=
  le_sub_of_add_le h

private theorem two_plus_n_sub_two_eq {n : Nat} (h : 2 ≤ n) : 2 + (n - 2) = n :=
  add_sub_of_le h

private theorem add_ge_four_of_each_ge_two {a b : Nat}
    (ha : 2 ≤ a) (hb : 2 ≤ b) : 4 ≤ a + b :=
  Nat.add_le_add ha hb

end E213.Theory.Atomicity.NonDecomposable

namespace E213.Theory.Atomicity.NonDecomposable

/-- **Characterization of atoms.** The non-decomposable integers
    `≥ 2` are exactly `{2, 3}`. -/
theorem non_decomposable_iff (n : Nat) :
    NonDecomposable n ↔ n = 2 ∨ n = 3 := by
  constructor
  · intro ⟨hge, hnd⟩
    match Nat.lt_or_ge n 4 with
    | Or.inl hlt => exact two_or_three_of_lt_four hge hlt
    | Or.inr hge4 =>
      exfalso
      apply hnd
      refine ⟨2, n - 2, Nat.le_refl _, ?_, ?_⟩
      · exact n_sub_two_ge_two_of_ge_four hge4
      · exact two_plus_n_sub_two_eq (Nat.le_trans (by decide) hge4)
  · intro h
    match h with
    | Or.inl h2 =>
      refine ⟨h2 ▸ Nat.le_refl 2, ?_⟩
      intro ⟨a, b, ha, hb, hab⟩
      have h4 : 4 ≤ a + b := add_ge_four_of_each_ge_two ha hb
      have hcontra : 4 ≤ 2 := h2 ▸ hab ▸ h4
      exact absurd hcontra (by decide)
    | Or.inr h3 =>
      refine ⟨h3 ▸ (by decide : (2:Nat) ≤ 3), ?_⟩
      intro ⟨a, b, ha, hb, hab⟩
      have h4 : 4 ≤ a + b := add_ge_four_of_each_ge_two ha hb
      have hcontra : 4 ≤ 3 := h3 ▸ hab ▸ h4
      exact absurd hcontra (by decide)

end E213.Theory.Atomicity.NonDecomposable
