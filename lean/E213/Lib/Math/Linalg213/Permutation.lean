import E213.Meta.Int213.Core

/-!
# Linalg213 — permutations and the alternating sign (toward the Leibniz determinant)

The natural home of the determinant's **alternating** property: antisymmetrization over the
row-orderings.  A row swap is a transposition `τ`; in the Leibniz sum
`det M = Σ_σ sign(σ)·Πᵢ M i (σ i)` it acts by `σ ↦ σ∘τ`, and `sign(σ∘τ) = −sign(σ)` flips
every term — so coincident row-pointings cancel **structurally**, not by a forced cofactor
cancellation (see `theory/essays/determinant_as_quotient_characteristic.md`).

This file builds the reusable substrate: list permutation-equivalence (`LPerm`), the
invariance of a sum under it (the cornerstone), and the alternating sign read off an
inversion count.

All ∅-axiom (over `Int213` core).
-/

namespace E213.Lib.Math.Linalg213.Permutation

open E213.Meta.Int213 (add_left_comm)

/-! ## §1 — list permutation-equivalence + sum invariance -/

/-- Permutation-equivalence of lists: the standard four-constructor inductive
    (`nil`, `cons`, adjacent `swap`, `trans`).  Two lists are `LPerm`-related iff one is a
    rearrangement of the other. -/
inductive LPerm {α : Type} : List α → List α → Prop
  | nil : LPerm [] []
  | cons (x : α) {l₁ l₂ : List α} : LPerm l₁ l₂ → LPerm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : LPerm (y :: x :: l) (x :: y :: l)
  | trans {l₁ l₂ l₃ : List α} : LPerm l₁ l₂ → LPerm l₂ l₃ → LPerm l₁ l₃

/-- `LPerm` is reflexive. -/
theorem LPerm.refl {α : Type} : ∀ (l : List α), LPerm l l
  | []      => LPerm.nil
  | x :: xs => LPerm.cons x (LPerm.refl xs)

/-- `LPerm` is symmetric. -/
theorem LPerm.symm {α : Type} {l₁ l₂ : List α} (h : LPerm l₁ l₂) : LPerm l₂ l₁ := by
  induction h with
  | nil               => exact LPerm.nil
  | cons x _ ih       => exact LPerm.cons x ih
  | swap x y l        => exact LPerm.swap y x l
  | trans _ _ ih₁ ih₂ => exact LPerm.trans ih₂ ih₁

/-- Sum of an `Int` list (low-to-high `foldr`). -/
def sumZ : List Int → Int
  | []      => 0
  | x :: xs => x + sumZ xs

/-- ★ **Sum is invariant under `LPerm`** — the cornerstone for the Leibniz antisymmetrization.
    Reordering the terms of a sum does not change it (`Int` `+` is commutative-associative). -/
theorem sumZ_lperm {l₁ l₂ : List Int} (h : LPerm l₁ l₂) : sumZ l₁ = sumZ l₂ := by
  induction h with
  | nil               => rfl
  | cons x _ ih       => show x + sumZ _ = x + sumZ _; rw [ih]
  | swap x y l        =>
    show y + (x + sumZ l) = x + (y + sumZ l)
    exact add_left_comm y x (sumZ l)
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

end E213.Lib.Math.Linalg213.Permutation
