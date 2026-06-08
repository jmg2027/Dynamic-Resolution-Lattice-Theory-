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
  (swapAt swapAt_prefix swapAt_lperm psign psign_swap_prefix LPerm perms iota
   inversions ltCount ltCount_append ltCount_cons2_comm)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList map_append')
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

/-! ## §3 — directed inversion-decrease + `composeList` structural laws -/

/-- The inversion-rearrangement `(1+p)+(q+c) = ((0+q)+(p+c))+1`. -/
private theorem ac1 (p q c : Nat) : (1 + p) + (q + c) = ((0 + q) + (p + c)) + 1 := by
  rw [Nat.zero_add, Nat.add_assoc q (p + c) 1, Nat.add_assoc p c 1,
      Nat.add_comm 1 p, Nat.add_assoc p 1 (q + c), Nat.add_comm 1 (q + c),
      Nat.add_assoc q c 1, Nat.add_left_comm p q (c + 1)]

/-- ★ **Directed inversion-decrease**: putting an out-of-order adjacent pair `y > x` in order
    (`pre ++ y :: x :: l ↦ pre ++ x :: y :: l`) removes exactly one inversion. -/
theorem inv_prefix_swap : ∀ (pre : List Nat) (y x : Nat) (l : List Nat), x < y →
    inversions (pre ++ y :: x :: l) = inversions (pre ++ x :: y :: l) + 1
  | [],       y, x, l, hxy => by
    have hnyx : ¬ y < x := fun h => Nat.lt_irrefl x (Nat.lt_trans hxy h)
    show ((if x < y then 1 else 0) + ltCount y l) + (ltCount x l + inversions l)
       = (((if y < x then 1 else 0) + ltCount x l) + (ltCount y l + inversions l)) + 1
    rw [if_pos hxy, if_neg hnyx]
    exact ac1 (ltCount y l) (ltCount x l) (inversions l)
  | a :: pre, y, x, l, hxy => by
    show ltCount a (pre ++ y :: x :: l) + inversions (pre ++ y :: x :: l)
       = (ltCount a (pre ++ x :: y :: l) + inversions (pre ++ x :: y :: l)) + 1
    rw [ltCount_append a pre (y :: x :: l), ltCount_append a pre (x :: y :: l),
        ltCount_cons2_comm a x y l, inv_prefix_swap pre y x l hxy, ← Nat.add_assoc]

/-- `σ ∘ (a :: l) = σ a :: (σ ∘ l)`. -/
theorem composeList_cons (σ : List Nat) (a : Nat) (l : List Nat) :
    composeList σ (a :: l) = σ.getD a 0 :: composeList σ l := rfl

/-- `σ ∘ (L ++ M) = (σ ∘ L) ++ (σ ∘ M)`. -/
theorem composeList_append (σ L M : List Nat) :
    composeList σ (L ++ M) = composeList σ L ++ composeList σ M :=
  map_append' (fun t => σ.getD t 0) L M

end E213.Lib.Math.Algebra.Linalg213.PermSign
