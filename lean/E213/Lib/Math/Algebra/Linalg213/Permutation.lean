import E213.Meta.Int213.Core
import E213.Lib.Math.Algebra.Linalg213.DetN

/-!
# Linalg213 — permutations and the alternating sign (toward the Leibniz determinant)

The natural home of the determinant's **alternating** property: antisymmetrization over the
row-orderings.  A row swap is a transposition `τ`; in the Leibniz sum
`det M = Σ_σ sign(σ)·Πᵢ M i (σ i)` it acts by `σ ↦ σ∘τ`, and `sign(σ∘τ) = −sign(σ)` flips
every term — so coincident row-pointings cancel **structurally**, not by a forced cofactor
cancellation (see `theory/essays/algebra/determinant_as_quotient_characteristic.md`).

This file builds the reusable substrate: list permutation-equivalence (`LPerm`), the
invariance of a sum under it (the cornerstone), and the alternating sign read off an
inversion count.

All ∅-axiom (over `Int213` core).
-/

namespace E213.Lib.Math.Algebra.Linalg213.Permutation

open E213.Meta.Int213 (add_left_comm mul_neg neg_mul neg_add mul_comm mul_assoc mul_left_comm)

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

open E213.Lib.Math.Algebra.Linalg213.DetN (altSign altSign_add)

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

/-! ## §3 — the positional sign flip (swap at any depth, via a prefix)

Lifting `psign_swap_adj` (head swap) to a swap of two adjacent entries *after any prefix*.  A
prefix `a` multiplies both signs by the same `altSign (ltCount a …)` — equal because the two
lists are multiset-equal across the swap — so the flip survives.  This is the bridge from
"adjacent value swap" to "swap rows `i, i+1` of a matrix". -/

/-- `ltCount` distributes over append. -/
theorem ltCount_append (a : Nat) : ∀ (L M : List Nat),
    ltCount a (L ++ M) = ltCount a L + ltCount a M
  | [],      M => by show ltCount a M = 0 + ltCount a M; rw [Nat.zero_add]
  | y :: ys, M => by
    show (if y < a then 1 else 0) + ltCount a (ys ++ M)
       = ((if y < a then 1 else 0) + ltCount a ys) + ltCount a M
    rw [ltCount_append a ys M, Nat.add_assoc]

/-- Swapping the first two entries leaves `ltCount` unchanged (multiset-invariant). -/
theorem ltCount_cons2_comm (a x y : Nat) (l : List Nat) :
    ltCount a (y :: x :: l) = ltCount a (x :: y :: l) :=
  Nat.add_left_comm (if y < a then 1 else 0) (if x < a then 1 else 0) (ltCount a l)

/-- `psign` peels a head via `altSign` of its inversion contribution: a clean factorization. -/
theorem psign_cons (a : Nat) (L : List Nat) :
    psign (a :: L) = altSign (ltCount a L) * psign L :=
  altSign_add (ltCount a L) (inversions L)

/-- ★ **Positional sign flip.**  Swapping two distinct adjacent entries after any prefix flips
    the sign: `psign (pre ++ y :: x :: l) = − psign (pre ++ x :: y :: l)` for `x ≠ y`. -/
theorem psign_swap_prefix (pre : List Nat) {x y : Nat} (l : List Nat) (h : x ≠ y) :
    psign (pre ++ y :: x :: l) = - psign (pre ++ x :: y :: l) := by
  induction pre with
  | nil          => exact psign_swap_adj l h
  | cons a pre ih =>
    show psign (a :: (pre ++ y :: x :: l)) = - psign (a :: (pre ++ x :: y :: l))
    rw [psign_cons a (pre ++ y :: x :: l), psign_cons a (pre ++ x :: y :: l), ih,
        ltCount_append a pre (y :: x :: l), ltCount_append a pre (x :: y :: l),
        ltCount_cons2_comm a x y l, mul_neg]

/-! ## §4 — the Leibniz determinant + assembly lemmas

`det M = Σ_σ sign(σ)·Πᵢ M i (σ i)`, summing over the explicit enumeration of permutation value
lists.  The two assembly lemmas (`sumZ_map_neg`, `map_lperm`) plus `psign_swap_prefix` reduce
the alternating property to "the enumeration is closed under a position-swap up to `LPerm`". -/

/-- Diagonal product selected by a value list, from row `i`: `M i p₀ · M (i+1) p₁ · …`. -/
def prodDiagFrom (M : Nat → Nat → Int) : Nat → List Nat → Int
  | _, []      => 1
  | i, p :: ps => M i p * prodDiagFrom M (i + 1) ps

/-- The Leibniz term for a permutation value list: `sign · diagonal product`. -/
def leibTerm (M : Nat → Nat → Int) (p : List Nat) : Int := psign p * prodDiagFrom M 0 p

/-- Insert `x` into every position of a list (the enumeration step). -/
def insertEverywhere (x : Nat) : List Nat → List (List Nat)
  | []      => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (fun l => y :: l)

/-- All permutation value lists of a list. -/
def permsOf : List Nat → List (List Nat)
  | []      => [[]]
  | x :: xs => (permsOf xs).flatMap (insertEverywhere x)

/-- `[0, 1, …, n−1]` (clean recursion: `iota (n+1) = iota n ++ [n]` by `rfl`). -/
def iota : Nat → List Nat
  | 0     => []
  | n + 1 => iota n ++ [n]

/-- All permutation value lists of `[0,…,n−1]`. -/
def perms (n : Nat) : List (List Nat) := permsOf (iota n)

/-- The **Leibniz determinant**: `Σ_σ sign(σ)·Πᵢ M i (σ i)`. -/
def leibDet (n : Nat) (M : Nat → Nat → Int) : Int := sumZ ((perms n).map (leibTerm M))

/-- Sanity: `2×2` identity-like matrix has determinant `1` (the enumeration + sign compute). -/
theorem leibDet_two_id : leibDet 2 (fun i j => if i = j then (1 : Int) else 0) = 1 := rfl

/-- A pointwise-negated sum negates. -/
theorem sumZ_map_neg {α : Type} (g : α → Int) : ∀ (L : List α),
    sumZ (L.map (fun a => -(g a))) = - sumZ (L.map g)
  | []      => rfl
  | a :: as => by
    show -(g a) + sumZ (as.map (fun a => -(g a))) = -(g a + sumZ (as.map g))
    rw [sumZ_map_neg g as, neg_add]

/-- `map` is an `LPerm` congruence. -/
theorem map_lperm {α β : Type} (f : α → β) {L1 L2 : List α} (h : LPerm L1 L2) :
    LPerm (L1.map f) (L2.map f) := by
  induction h with
  | nil               => exact LPerm.nil
  | cons x _ ih        => exact LPerm.cons (f x) ih
  | swap x y l         => exact LPerm.swap (f x) (f y) (l.map f)
  | trans _ _ ih₁ ih₂  => exact LPerm.trans ih₁ ih₂

/-! ## §5 — the per-term reindex (adjacent row swap negates each Leibniz term)

Swapping rows `k, k+1` of `M` maps the term at `pre ++ y :: x :: l` (`k = pre.length`) to the
**negation** of the term at the position-swapped list `pre ++ x :: y :: l`: the diagonal products
agree (two factors commute, `mul_left_comm`), and the sign flips (`psign_swap_prefix`).  This is
the determinant's core combinatorial content; the remaining gate is closure of `perms` under the
position-swap up to `LPerm`. -/

/-- `prodDiagFrom` splits over append (with the row offset advancing by the prefix length). -/
theorem prodDiagFrom_append (M : Nat → Nat → Int) : ∀ (i : Nat) (L R : List Nat),
    prodDiagFrom M i (L ++ R) = prodDiagFrom M i L * prodDiagFrom M (i + L.length) R
  | i, [],      R => by show prodDiagFrom M i R = 1 * prodDiagFrom M i R; rw [Int.one_mul]
  | i, p :: ps, R => by
    have hidx : (i + 1) + ps.length = i + (ps.length + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 ps.length]
    show M i p * prodDiagFrom M (i + 1) (ps ++ R)
       = (M i p * prodDiagFrom M (i + 1) ps) * prodDiagFrom M (i + (ps.length + 1)) R
    rw [prodDiagFrom_append M (i + 1) ps R, ← hidx, mul_assoc]

/-- Swap rows `k` and `k+1` of a matrix. -/
def rowSwapAt (k : Nat) (M : Nat → Nat → Int) : Nat → Nat → Int :=
  fun r c => if r = k then M (k + 1) c else if r = k + 1 then M k c else M r c

/-- `rowSwapAt` is unchanged on a row `r ≠ k, k+1`. -/
theorem rowSwapAt_other (k : Nat) (M : Nat → Nat → Int) {r : Nat} (h1 : r ≠ k) (h2 : r ≠ k + 1)
    (c : Nat) : rowSwapAt k M r c = M r c := by
  show (if r = k then M (k + 1) c else if r = k + 1 then M k c else M r c) = M r c
  rw [if_neg h1, if_neg h2]

/-- Below the swap (`rows < k`): `prodDiagFrom` is unaffected. -/
theorem prodDiagFrom_eq_below (k : Nat) (M : Nat → Nat → Int) : ∀ (i : Nat) (p : List Nat),
    i + p.length ≤ k → prodDiagFrom (rowSwapAt k M) i p = prodDiagFrom M i p
  | _, [],      _ => rfl
  | i, q :: qs, h => by
    have hik : i < k :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos qs.length)) h
    have hile : (i + 1) + qs.length ≤ k := by
      rw [Nat.add_assoc, Nat.add_comm 1 qs.length]; exact h
    show rowSwapAt k M i q * prodDiagFrom (rowSwapAt k M) (i + 1) qs
       = M i q * prodDiagFrom M (i + 1) qs
    rw [rowSwapAt_other k M (Nat.ne_of_lt hik) (Nat.ne_of_lt (Nat.lt_trans hik (Nat.lt_succ_self k))),
        prodDiagFrom_eq_below k M (i + 1) qs hile]

/-- Above the swap (`rows ≥ k+2`): `prodDiagFrom` is unaffected. -/
theorem prodDiagFrom_eq_above (k : Nat) (M : Nat → Nat → Int) : ∀ (i : Nat) (p : List Nat),
    k + 2 ≤ i → prodDiagFrom (rowSwapAt k M) i p = prodDiagFrom M i p
  | _, [],      _ => rfl
  | i, q :: qs, h => by
    have hki : k < i := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_trans (Nat.le_succ _) h)
    have hk1i : k + 1 < i := Nat.lt_of_lt_of_le (Nat.lt_succ_self (k + 1)) h
    show rowSwapAt k M i q * prodDiagFrom (rowSwapAt k M) (i + 1) qs
       = M i q * prodDiagFrom M (i + 1) qs
    rw [rowSwapAt_other k M (Ne.symm (Nat.ne_of_lt hki)) (Ne.symm (Nat.ne_of_lt hk1i)),
        prodDiagFrom_eq_above k M (i + 1) qs (Nat.le_trans h (Nat.le_succ i))]

/-- `rowSwapAt` at the swapped row `k` reads row `k+1`. -/
theorem rowSwapAt_at (k : Nat) (M : Nat → Nat → Int) (c : Nat) :
    rowSwapAt k M k c = M (k + 1) c := by
  show (if k = k then M (k + 1) c else if k = k + 1 then M k c else M k c) = M (k + 1) c
  rw [if_pos rfl]

/-- `rowSwapAt` at `k+1` reads row `k`. -/
theorem rowSwapAt_at1 (k : Nat) (M : Nat → Nat → Int) (c : Nat) :
    rowSwapAt k M (k + 1) c = M k c := by
  show (if k + 1 = k then M (k + 1) c else if k + 1 = k + 1 then M k c else M (k + 1) c) = M k c
  rw [if_neg (Nat.ne_of_lt (Nat.lt_succ_self k)).symm, if_pos rfl]

/-- The diagonal products of `M` (at the position-swapped list) and of `rowSwapAt k M` agree:
    the two affected factors commute (`mul_left_comm`); the rest match. -/
theorem prodDiag_rowSwap (M : Nat → Nat → Int) (pre : List Nat) (x y : Nat) (l : List Nat) :
    prodDiagFrom (rowSwapAt pre.length M) 0 (pre ++ y :: x :: l)
      = prodDiagFrom M 0 (pre ++ x :: y :: l) := by
  rw [prodDiagFrom_append (rowSwapAt pre.length M) 0 pre (y :: x :: l),
      prodDiagFrom_append M 0 pre (x :: y :: l),
      prodDiagFrom_eq_below pre.length M 0 pre (Nat.le_of_eq (Nat.zero_add pre.length)),
      Nat.zero_add]
  show prodDiagFrom M 0 pre * (rowSwapAt pre.length M pre.length y *
         (rowSwapAt pre.length M (pre.length + 1) x *
           prodDiagFrom (rowSwapAt pre.length M) (pre.length + 2) l))
     = prodDiagFrom M 0 pre *
         (M pre.length x * (M (pre.length + 1) y * prodDiagFrom M (pre.length + 2) l))
  rw [rowSwapAt_at, rowSwapAt_at1,
      prodDiagFrom_eq_above pre.length M (pre.length + 2) l (Nat.le_refl _),
      mul_left_comm (M (pre.length + 1) y)]

/-- ★ **Per-term identity.**  An adjacent row swap (rows `k = pre.length`, `k+1`) sends the
    Leibniz term at `pre ++ y :: x :: l` to the negation of the term at `pre ++ x :: y :: l`
    (for `x ≠ y`).  The diagonal products agree; the sign flips. -/
theorem leibTerm_rowSwap (M : Nat → Nat → Int) (pre : List Nat) {x y : Nat} (l : List Nat)
    (h : x ≠ y) :
    leibTerm (rowSwapAt pre.length M) (pre ++ y :: x :: l)
      = - leibTerm M (pre ++ x :: y :: l) := by
  show psign (pre ++ y :: x :: l) * prodDiagFrom (rowSwapAt pre.length M) 0 (pre ++ y :: x :: l)
     = -(psign (pre ++ x :: y :: l) * prodDiagFrom M 0 (pre ++ x :: y :: l))
  rw [prodDiag_rowSwap, psign_swap_prefix pre l h, neg_mul]

/-! ## §6 — the position-swap operation `swapAt`

The list-level adjacent transposition: `swapAt k` swaps entries at positions `k, k+1`.  It is
an `LPerm` (`swapAt_lperm`) and realizes the prefix decomposition (`swapAt_prefix`), tying the
per-term identity to a single operation that the enumeration-closure (next file) reasons about. -/

/-- Swap the entries at positions `k` and `k+1` of a list. -/
def swapAt (k : Nat) (p : List Nat) : List Nat :=
  match p with
  | []     => []
  | a :: r =>
    match k, r with
    | 0,      b :: r' => b :: a :: r'
    | 0,      []      => [a]
    | k' + 1, _       => a :: swapAt k' r

/-- `swapAt k` is a list permutation (`LPerm`). -/
theorem swapAt_lperm (k : Nat) (p : List Nat) : LPerm (swapAt k p) p := by
  induction p generalizing k with
  | nil => cases k <;> exact LPerm.nil
  | cons a r ih =>
    cases k with
    | zero =>
      cases r with
      | nil       => exact LPerm.cons a LPerm.nil
      | cons b r' => exact LPerm.swap a b r'
    | succ k => exact LPerm.cons a (ih k)

/-- `swapAt` at `pre.length` on `pre ++ y :: x :: l` swaps `y` and `x`. -/
theorem swapAt_prefix : ∀ (pre : List Nat) (y x : Nat) (l : List Nat),
    swapAt pre.length (pre ++ y :: x :: l) = pre ++ x :: y :: l
  | [],        y, x, l => rfl
  | a :: pre,  y, x, l => by
    show a :: swapAt pre.length (pre ++ y :: x :: l) = a :: (pre ++ x :: y :: l)
    rw [swapAt_prefix pre y x l]

end E213.Lib.Math.Algebra.Linalg213.Permutation
