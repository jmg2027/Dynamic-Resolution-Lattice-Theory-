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
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (permsOf_sound permsOf_complete lperm_of_cnt_eq cnt_lperm add_left_cancel'
   nodup_iota lt_of_mem_iota perm_length)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (iota_cons)
open E213.Meta.Int213 (mul_neg neg_mul)

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

/-! ## §4 — adjacent-sortedness and descent existence -/

/-- Adjacent-sortedness (`a ≤ b` for every adjacent pair). -/
def Sorted : List Nat → Prop
  | []          => True
  | [_]         => True
  | a :: b :: t => a ≤ b ∧ Sorted (b :: t)

/-- A sorted list's head is `≤` every later entry. -/
theorem sorted_head_le : ∀ (a : Nat) (t : List Nat), Sorted (a :: t) → ∀ v, v ∈ t → a ≤ v
  | _, [],     _, v, hv => nomatch hv
  | a, b :: t, h, v, hv => by
    obtain ⟨hab, hbt⟩ := h
    cases hv with
    | head      => exact hab
    | tail _ hv' => exact Nat.le_trans hab (sorted_head_le b t hbt v hv')

/-- `ltCount a t = 0` when `a ≤` every entry of `t`. -/
theorem ltCount_zero_of_all_ge (a : Nat) : ∀ (t : List Nat), (∀ v, v ∈ t → a ≤ v) → ltCount a t = 0
  | [],     _ => rfl
  | b :: t, h => by
    show (if b < a then 1 else 0) + ltCount a t = 0
    rw [if_neg (Nat.not_lt.mpr (h b (List.Mem.head _))), Nat.zero_add]
    exact ltCount_zero_of_all_ge a t (fun v hv => h v (List.Mem.tail _ hv))

/-- A sorted list has no inversions. -/
theorem sorted_imp_inv_zero : ∀ (τ : List Nat), Sorted τ → inversions τ = 0
  | [],          _ => rfl
  | [_],         _ => rfl
  | a :: b :: t, h => by
    obtain ⟨hab, hbt⟩ := h
    show ltCount a (b :: t) + inversions (b :: t) = 0
    rw [sorted_imp_inv_zero (b :: t) hbt, Nat.add_zero,
        ltCount_zero_of_all_ge a (b :: t) (fun v hv => by
          cases hv with
          | head      => exact hab
          | tail _ hv' => exact Nat.le_trans hab (sorted_head_le b t hbt v hv'))]

/-- ★ **Sorted-or-descent**: every list is adjacent-sorted or has an out-of-order adjacent pair. -/
theorem sorted_or_descent : ∀ (τ : List Nat),
    Sorted τ ∨ ∃ pre y x l, τ = pre ++ y :: x :: l ∧ x < y
  | []          => Or.inl trivial
  | [_]         => Or.inl trivial
  | a :: b :: t => by
    rcases sorted_or_descent (b :: t) with hs | ⟨pre, y, x, l, he, hxy⟩
    · rcases Nat.lt_or_ge b a with hba | hab
      · exact Or.inr ⟨[], a, b, t, rfl, hba⟩
      · exact Or.inl ⟨hab, hs⟩
    · exact Or.inr ⟨a :: pre, y, x, l, congrArg (a :: ·) he, hxy⟩

/-- ★ **Descent existence**: a list with an inversion has an out-of-order adjacent pair. -/
theorem descent_of_inv_pos (τ : List Nat) (h : inversions τ ≠ 0) :
    ∃ pre y x l, τ = pre ++ y :: x :: l ∧ x < y := by
  rcases sorted_or_descent τ with hs | hd
  · exact absurd (sorted_imp_inv_zero τ hs) h
  · exact hd

/-! ## §5 — the swap-invariant `psign(σ∘τ)·psign τ` -/

/-- ★★ **The step invariant**: `psign(σ∘τ)·psign τ` is unchanged by swapping an adjacent pair
    (`pre ++ y :: x :: l ↦ pre ++ x :: y :: l`), provided the entries and their `σ`-images differ.
    Both factors flip sign (`psign_swap_prefix` on `τ` and on `σ∘τ`), so the product is preserved —
    this makes the value `psign(σ∘τ)·psign τ` an invariant of the bubble-sort reduction. -/
theorem Q_swap (σ pre : List Nat) (y x : Nat) (l : List Nat) (hxy : x ≠ y)
    (hne : σ.getD x 0 ≠ σ.getD y 0) :
    psign (composeList σ (pre ++ y :: x :: l)) * psign (pre ++ y :: x :: l)
      = psign (composeList σ (pre ++ x :: y :: l)) * psign (pre ++ x :: y :: l) := by
  rw [composeList_append σ pre (y :: x :: l), composeList_append σ pre (x :: y :: l),
      composeList_cons σ y (x :: l), composeList_cons σ x l,
      composeList_cons σ x (y :: l), composeList_cons σ y l,
      psign_swap_prefix (composeList σ pre) (composeList σ l) hne,
      psign_swap_prefix pre l hxy, neg_mul, mul_neg, Int.neg_neg]

/-! ## §6 — a sorted permutation of `iota n` is `iota n` (the base case) -/

/-- The tail of a sorted list is sorted. -/
theorem sorted_tail : ∀ {a : Nat} {t : List Nat}, Sorted (a :: t) → Sorted t
  | _, [],     _ => trivial
  | _, _ :: _, h => h.2

/-- A sorted list's head is `≤` every entry (including itself). -/
theorem sorted_head_le_self {a : Nat} {t : List Nat} (h : Sorted (a :: t)) :
    ∀ v, v ∈ a :: t → a ≤ v := by
  intro v hv
  cases hv with
  | head       => exact Nat.le_refl a
  | tail _ hv' => exact sorted_head_le a t h v hv'

/-- `LPerm` cons-cancellation (`z :: a ~ z :: b ⟹ a ~ b`). -/
theorem lperm_cons_inv {z : Nat} {a b : List Nat} (h : LPerm (z :: a) (z :: b)) : LPerm a b := by
  apply lperm_of_cnt_eq
  intro w
  exact add_left_cancel' (if z = w then 1 else 0) (cnt_lperm (a := w) h)

/-- ★ **Two sorted lists with the same multiset are equal**. -/
theorem sorted_lperm_eq : ∀ (a b : List Nat), Sorted a → Sorted b → LPerm a b → a = b
  | [],     [],     _,   _,   _ => rfl
  | [],     _ :: _, _,   _,   h => nomatch (PermClosure.LPerm.length_eq h)
  | _ :: _, [],     _,   _,   h => nomatch (PermClosure.LPerm.length_eq h)
  | p :: a, q :: b, hsa, hsb, h => by
    have hpq : p = q :=
      Nat.le_antisymm
        (sorted_head_le_self hsa q (PermClosure.LPerm.mem (Permutation.LPerm.symm h) (List.Mem.head _)))
        (sorted_head_le_self hsb p (PermClosure.LPerm.mem h (List.Mem.head _)))
    subst hpq
    rw [sorted_lperm_eq a b (sorted_tail hsa) (sorted_tail hsb) (lperm_cons_inv h)]

/-- `map (·+1)` preserves sortedness. -/
theorem sorted_map_succ : ∀ (L : List Nat), Sorted L → Sorted (L.map Nat.succ)
  | [],          _ => trivial
  | [_],         _ => trivial
  | a :: b :: t, h => ⟨Nat.succ_le_succ h.1, sorted_map_succ (b :: t) h.2⟩

/-- Prepend a head `≤` every entry to a sorted list. -/
theorem sorted_cons (a : Nat) : ∀ {M : List Nat}, (∀ c, c ∈ M → a ≤ c) → Sorted M → Sorted (a :: M)
  | [],     _,  _  => trivial
  | c :: _, hc, hM => ⟨hc c (List.Mem.head _), hM⟩

/-- `iota n` is sorted. -/
theorem sorted_iota : ∀ n, Sorted (iota n)
  | 0     => trivial
  | n + 1 => by
    rw [iota_cons n]
    exact sorted_cons 0 (fun c _ => Nat.zero_le c) (sorted_map_succ (iota n) (sorted_iota n))

/-- ★★ **A sorted permutation of `iota n` is `iota n`** — the base case for `psign_mul`. -/
theorem sorted_perm_eq_iota (n : Nat) (τ : List Nat) (hs : Sorted τ) (hτ : τ ∈ perms n) :
    τ = iota n :=
  sorted_lperm_eq τ (iota n) hs (sorted_iota n) (permsOf_sound (iota n) τ hτ)

end E213.Lib.Math.Algebra.Linalg213.PermSign
