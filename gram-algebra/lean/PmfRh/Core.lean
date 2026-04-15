/-
  DRLT Core Theorems — Pure Lean 4 (No Mathlib)
  Mingu Jeong & Claude (Anthropic), 2026.04.15

  Machine-verified proofs using ONLY Lean 4 core.
-/

/-! ## 1. Additive Atoms -/

def isAdditiveAtom (n : Nat) : Prop :=
  2 ≤ n ∧ ¬∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧ a + b = n

theorem additive_atoms (n : Nat) :
    isAdditiveAtom n ↔ n = 2 ∨ n = 3 := by
  unfold isAdditiveAtom
  constructor
  · intro ⟨h_ge, h_no⟩
    match Nat.decEq n 2 with
    | .isTrue h => exact Or.inl h
    | .isFalse h2 =>
      match Nat.decEq n 3 with
      | .isTrue h => exact Or.inr h
      | .isFalse h3 =>
        exact absurd ⟨2, n - 2, by omega, by omega, by omega⟩ h_no
  · intro h
    match h with
    | Or.inl h => subst h; exact ⟨by omega, fun ⟨a, b, ha, hb, hab⟩ => by omega⟩
    | Or.inr h => subst h; exact ⟨by omega, fun ⟨a, b, ha, hb, hab⟩ => by omega⟩

/-! ## 2. Doubly Irreducible -/

def isExtensionAtom (n : Nat) : Prop := n = 2

def isDoublyIrreducible (n : Nat) : Prop :=
  isAdditiveAtom n ∧ isExtensionAtom n

theorem unique_doubly_irreducible (n : Nat) :
    isDoublyIrreducible n ↔ n = 2 := by
  unfold isDoublyIrreducible isExtensionAtom
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; subst h
    exact ⟨(additive_atoms 2).mpr (Or.inl rfl), rfl⟩

/-! ## 3. Self-Contradiction -/

structure ResolutionSeq where
  δ : Nat → Nat
  pos : ∀ n, 0 < δ n

theorem self_contradiction (rs : ResolutionSeq) :
    ∀ n, rs.δ n ≠ 0 := by
  intro n
  exact Nat.not_eq_zero_of_lt (rs.pos n)

/-! ## 4. Two Boundaries -/

theorem two_boundaries (d : Nat) :
    2 = d ↔ d = 2 := by
  constructor
  · intro h; exact h.symm
  · intro h; exact h.symm

/-! ## 5. Proof Levels -/

inductive ProofLevel where
  | deduction | induction | limit

def ProofLevel.isClosed : ProofLevel → Bool
  | .deduction => true
  | .induction => false
  | .limit => false

theorem only_deduction_closes (p : ProofLevel) :
    p.isClosed = true ↔ p = .deduction := by
  cases p <;> simp [ProofLevel.isClosed]
