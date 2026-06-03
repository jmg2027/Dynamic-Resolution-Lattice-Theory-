import E213.Meta.Int213.Core
import E213.Lib.Math.Linalg213.DetN

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

/-! ## §2 — inversion count, sign, and the adjacent-transposition sign flip

A permutation is carried as its value list `[σ 0, σ 1, …]`.  Its **sign** is `(−1)` to the
**inversion count** (`DetN.altSign`).  The payoff: an adjacent swap of two *distinct* values
flips the sign — `sign(σ∘τ) = −sign σ` for an adjacent transposition `τ`, the structural fact
the determinant essay names as alternating's natural home. -/

open E213.Lib.Math.Linalg213.DetN (altSign)

/-- Inversions contributed by `x` against a tail: the count of later entries `< x`. -/
def ltCount (x : Nat) : List Nat → Nat
  | []      => 0
  | y :: ys => (if y < x then 1 else 0) + ltCount x ys

/-- Total inversion count of a value list (pairs out of order). -/
def inversions : List Nat → Nat
  | []      => 0
  | x :: xs => ltCount x xs + inversions xs

/-- The sign of a permutation value list: `(−1)` to the inversion count. -/
def psign (l : List Nat) : Int := altSign (inversions l)

/-- `altSign` step: `(−1)^(n+1) = −(−1)^n`. -/
private theorem altSign_succ (n : Nat) : altSign (n + 1) = -(altSign n) := rfl

/-- The shared inversion-rearrangement: `(1 + p) + (q + c) = ((0 + q) + (p + c)) + 1`. -/
private theorem ac_form (p q c : Nat) :
    (1 + p) + (q + c) = ((0 + q) + (p + c)) + 1 := by
  rw [Nat.zero_add, Nat.add_assoc q (p + c) 1, Nat.add_assoc p c 1,
      Nat.add_comm 1 p, Nat.add_assoc p 1 (q + c), Nat.add_comm 1 (q + c),
      Nat.add_assoc q c 1, Nat.add_left_comm p q (c + 1)]

/-- ★ **An adjacent transposition of distinct values flips the sign.**
    `psign (y :: x :: l) = − psign (x :: y :: l)` when `x ≠ y` — the concrete
    `sign(σ∘τ) = −sign σ` for an adjacent `τ`, the engine of the alternating property. -/
theorem psign_swap_adj {x y : Nat} (l : List Nat) (h : x ≠ y) :
    psign (y :: x :: l) = - psign (x :: y :: l) := by
  rcases Nat.lt_or_ge x y with hxy | hge
  · -- x < y
    have hnyx : ¬ y < x := fun hyx => Nat.lt_irrefl x (Nat.lt_trans hxy hyx)
    have key : inversions (y :: x :: l) = inversions (x :: y :: l) + 1 := by
      show ((if x < y then 1 else 0) + ltCount y l) + (ltCount x l + inversions l)
         = (((if y < x then 1 else 0) + ltCount x l) + (ltCount y l + inversions l)) + 1
      rw [if_pos hxy, if_neg hnyx]
      exact ac_form (ltCount y l) (ltCount x l) (inversions l)
    show altSign (inversions (y :: x :: l)) = - altSign (inversions (x :: y :: l))
    rw [key, altSign_succ]
  · -- y < x (from y ≤ x and x ≠ y)
    have hyx : y < x := Nat.lt_of_le_of_ne hge (fun e => h e.symm)
    have hnxy : ¬ x < y := fun hxy => Nat.lt_irrefl y (Nat.lt_trans hyx hxy)
    have key : inversions (x :: y :: l) = inversions (y :: x :: l) + 1 := by
      show ((if y < x then 1 else 0) + ltCount x l) + (ltCount y l + inversions l)
         = (((if x < y then 1 else 0) + ltCount y l) + (ltCount x l + inversions l)) + 1
      rw [if_pos hyx, if_neg hnxy]
      exact ac_form (ltCount x l) (ltCount y l) (inversions l)
    show altSign (inversions (y :: x :: l)) = - altSign (inversions (x :: y :: l))
    rw [key, altSign_succ, Int.neg_neg]

end E213.Lib.Math.Linalg213.Permutation
