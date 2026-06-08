import E213.Lib.Math.Algebra.Linalg213.PermGroup
import E213.Lib.Math.Algebra.Linalg213.PermClosure

/-!
# Linalg213 — permutation sign multiplicativity (toward `det Mᵀ = det M`)

The sign theory's keystone: `psign (σ ∘ τ) = psign σ · psign τ`, from which `psign (σ⁻¹) = psign σ`
is a one-liner (`psign σ · psign σ⁻¹ = psign id = 1` in `{±1}`).  Both feed the transpose
determinant.

The proof bootstraps from the one combinatorial fact already in `Permutation`
(`psign_swap_prefix`: an adjacent transposition flips the sign) via the bubble-sort engine:
composition commutes with a position-swap (`composeList_swapAt`), so the inductive step is a
single sign-flip; the base case is `inversions τ = 0 ⟹ τ = iota n`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.PermSign

open E213.Lib.Math.Algebra.Linalg213.Permutation
  (swapAt swapAt_prefix swapAt_lperm psign psign_swap_prefix LPerm perms iota)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (permsOf_sound permsOf_complete)

/-! ## §1 — composition commutes with an adjacent position-swap -/

/-- `map` commutes with `swapAt` (a position-swap just rearranges, `map` is elementwise). -/
theorem map_swapAt (f : Nat → Nat) (k : Nat) (l : List Nat) :
    (swapAt k l).map f = swapAt k (l.map f) := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons a r ih =>
    cases k with
    | zero =>
      cases r with
      | nil       => rfl
      | cons b r' => rfl
    | succ k =>
      show f a :: (swapAt k r).map f = f a :: swapAt k (r.map f)
      rw [ih k]

/-- ★ `σ ∘ (swapAt k τ) = swapAt k (σ ∘ τ)` — composing with a position-swapped argument is the
    position-swap of the composite.  The inductive step's geometric content. -/
theorem composeList_swapAt (σ τ : List Nat) (k : Nat) :
    composeList σ (swapAt k τ) = swapAt k (composeList σ τ) :=
  map_swapAt (fun t => σ.getD t 0) k τ

/-! ## §2 — the sign of a position-swap, and `perms`-closure -/

/-- ★ **An adjacent position-swap flips the sign** (decomposed form): swapping the two distinct
    adjacent entries `y ≠ x` after any prefix negates `psign`.  The inductive step's sign content
    (`swapAt_prefix` realizes the swap; `psign_swap_prefix` flips). -/
theorem psign_swapAt (pre : List Nat) (y x : Nat) (l : List Nat) (h : y ≠ x) :
    psign (swapAt pre.length (pre ++ y :: x :: l)) = - psign (pre ++ y :: x :: l) := by
  rw [swapAt_prefix pre y x l, psign_swap_prefix pre l (Ne.symm h), Int.neg_neg]

/-- ★ **`perms` is closed under a position-swap**: `swapAt k τ` is again a permutation of
    `iota n` (it is `LPerm`-equal to `τ`). -/
theorem swapAt_mem_perms (n k : Nat) (τ : List Nat) (hτ : τ ∈ perms n) :
    swapAt k τ ∈ perms n :=
  permsOf_complete (iota n) (swapAt k τ)
    (LPerm.trans (swapAt_lperm k τ) (permsOf_sound (iota n) τ hτ))

end E213.Lib.Math.Algebra.Linalg213.PermSign
