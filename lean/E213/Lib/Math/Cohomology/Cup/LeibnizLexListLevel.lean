import E213.Lib.Math.Cohomology.Cup.LeibnizLexStructural

/-!
# Cup.LeibnizLexListLevel — list-level twisted Leibniz (PURE, ∀ k l)

Completion of the user's 3-way partition strategy at the **List
level** — bypasses `subsetIdx` / `Fin` indexing and proves the
self-referential Leibniz purely in terms of `List` operations.

The statement: for any `k, l : Nat`, any Bool-valued cochain
functions `α β : List Nat → Bool`, and any list `τ`:

  foldl xor (List.range (k+l+1)) (fun i => cupAt k l α β (τ.eraseIdx i))
    = xor (xor (foldl xor (List.range (k+1)) (fun i =>
                  cupAt k l α β-with-shift1))
               (foldl xor (List.range (l+1)) (fun j =>
                  cupAt k l α β-with-shift2)))
          (cupAt k l α β (τ.eraseIdx k))

In our framing:
  · cupAt k l α β τ := α(τ.take k) && β(τ.drop k)
  · δ at τ (list level) := foldl xor false (range (k+1))
                            (fun i => σ(τ.eraseIdx i))

The structural lemmas from `LeibnizLexStructural` (eraseIdx_take_low,
eraseIdx_drop_high, etc.) reduce each face's cup-value into a form
matching one of the three RHS blocks; foldl XOR partition then
assembles.

PURE.  No Mathlib, no omega, no decide enumeration — pure structural
induction on lists + Bool / Nat core.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel

open E213.Lib.Math.Cohomology.Cup.LeibnizLexStructural

/-! ## §1.  Foldl XOR algebra

Basic results about `List.foldl xor` over `List Nat`. -/

/-- ★ **Bool AND distributes over XOR (left)**: c && (a ⊕ b) = (c && a) ⊕ (c && b). -/
theorem and_xor_distrib_left (c a b : Bool) :
    (c && xor a b) = xor (c && a) (c && b) := by
  cases c <;> cases a <;> cases b <;> rfl

/-- ★ **foldl xor accumulates linearly**: foldl with accumulator
    `acc` equals XOR of `acc` with foldl from `false`.  PURE. -/
theorem foldl_xor_acc (f : Nat → Bool) (l : List Nat) (acc : Bool) :
    l.foldl (fun a i => xor a (f i)) acc
    = xor acc (l.foldl (fun a i => xor a (f i)) false) := by
  induction l generalizing acc with
  | nil => show acc = xor acc false; cases acc <;> rfl
  | cons x xs ih =>
    show xs.foldl (fun a i => xor a (f i)) (xor acc (f x))
        = xor acc (xs.foldl (fun a i => xor a (f i)) (xor false (f x)))
    rw [ih (xor acc (f x)), ih (xor false (f x))]
    show xor (xor acc (f x)) _ = xor acc (xor (xor false (f x)) _)
    cases acc <;> cases f x <;>
      cases xs.foldl (fun a i => xor a (f i)) false <;> rfl

/-- ★ **AND distributes over foldl XOR**: pulling a constant Bool
    `c` outside a foldl XOR.  PURE. -/
theorem and_distrib_foldl_xor (c : Bool) (f : Nat → Bool) (l : List Nat) :
    (c && l.foldl (fun a i => xor a (f i)) false)
    = l.foldl (fun a i => xor a (c && f i)) false := by
  induction l with
  | nil =>
    show (c && false) = false
    cases c <;> rfl
  | cons x xs ih =>
    show (c && xs.foldl (fun a i => xor a (f i)) (xor false (f x)))
       = xs.foldl (fun a i => xor a (c && f i)) (xor false (c && f x))
    rw [foldl_xor_acc f xs (xor false (f x))]
    rw [foldl_xor_acc (fun i => c && f i) xs (xor false (c && f x))]
    -- Goal: c && xor (xor false (f x)) FOLDfx = xor (xor false (c && f x)) FOLDcfx
    rw [and_xor_distrib_left c (xor false (f x))]
    -- Goal: xor (c && xor false (f x)) (c && FOLDfx) = xor (xor false (c && f x)) FOLDcfx
    rw [show (c && xor false (f x)) = xor false (c && f x) from by
        cases c <;> cases f x <;> rfl]
    -- Goal: xor (xor false (c && f x)) (c && FOLDfx) = xor (xor false (c && f x)) FOLDcfx
    rw [ih]

/-! ## §2.  Range split at position (deferred)

`List.range_succ` from Lean core (`List.range (n+1) = List.range n ++
[n]`) introduces `[propext]` axiom — depends on a stricter rewriting
chain inside the core library.  To keep strict PURE, we forgo the
named re-export here and inline the equivalence when needed.

The split-at-position pattern used in the 3-way partition assembly
is decomposed into the §1 foldl XOR algebra + per-instance index
calculation. -/

/-! ## §3.  List-level cup and delta operations

We define type-clean list-level analogs of `cup` and `delta` that
bypass `subsetIdx` / `Fin` indexing.  These are the "structural
core" — once the Leibniz holds at this level, transfer to the
Fin-indexed cup follows via `subsetIdx ↔ kSubset` round-trip
(deferred). -/

/-- List-level lex-projection cup at bidegree (k, l).
    α and β are cochains represented as `List Nat → Bool`. -/
def cupList (k _l : Nat) (α β : List Nat → Bool) (τ : List Nat) : Bool :=
  α (τ.take k) && β (τ.drop k)

/-- List-level coboundary at degree k.  σ : List Nat → Bool. -/
def deltaList (k : Nat) (σ : List Nat → Bool) (τ : List Nat) : Bool :=
  (List.range (k + 1)).foldl
    (fun acc i => xor acc (σ (τ.eraseIdx i)))
    false

/-! ## §4.  Status: list-level main theorem (assembly stub)

The full ∀ (k, l) list-level twisted Leibniz statement is:

  ∀ (k l : Nat) (α β : List Nat → Bool) (τ : List Nat),
    τ.length = k + l + 1 →
    deltaList (k+l) (cupList k l α β) τ
      = xor (xor (cupList (k+1) l (deltaList k α) β τ)
                 (cupList k (l+1) α (deltaList l β) τ))
            (cupList k l α β (τ.eraseIdx k))

Its proof assembles via:
  1. δ unfolding: `deltaList (k+l) (cupList k l α β) τ = foldl_xor
     over [0..k+l] of f(i) := cupList k l α β (τ.eraseIdx i)`
  2. For each i, apply `LeibnizLexStructural.eraseIdx_*_*` lemmas:
       - i < k: f(i) = α((τ.take(k+1)).eraseIdx i) · β(τ.drop(k+1))
       - i = k: f(i) = α(τ.take k) · β(τ.drop(k+1))  (= correction)
       - i > k: f(i) = α(τ.take k) · β((τ.drop k).eraseIdx (j+1))
  3. (δα⌣β) unfolds via §1 (AND distributes over foldl XOR) to a
     foldl_xor over [0..k] of α((τ.take(k+1)).eraseIdx i) · β(τ.drop(k+1)).
     Block 1 (i < k) matches f.  i = k inside (δα⌣β) gives
     α(τ.take k) · β(τ.drop(k+1)) = correction.
  4. (α⌣δβ) unfolds similarly; Block 3 (j > 0 → i = k+j) matches f
     for i > k.  j = 0 inside (α⌣δβ) ALSO gives correction.
  5. (δα⌣β) ⊕ (α⌣δβ) = Block 1 ⊕ correction ⊕ correction ⊕ Block 3
                       = Block 1 ⊕ Block 3 (correction cancels in ℤ/2)
  6. LHS = Block 1 ⊕ correction ⊕ Block 3
       = (Block 1 ⊕ Block 3) ⊕ correction
       = (δα⌣β ⊕ α⌣δβ) ⊕ correction.  ∎

The remaining technical content for the full Lean assembly is:
  · range-split at position k (3-block partition of List.range (k+l+1))
  · index reindexing (i = k + j + 1 ↔ j ∈ [0..l-1])

These are List combinatorics, all in principle expressible via
Lean 4 core induction.  Tagged for next-session completion. -/

/-! ## §5.  List-level (1, 1) twisted Leibniz — symbolic proof

We prove the (1, 1) case at the list level using the structural
lemmas (no `decide`, no `subsetIdx`).  This is the symbolic core
that generalises to ∀ (k, l) once the range-split + reindexing
are in place. -/

/-- ★★★ **List-level (1, 1) twisted Leibniz** — PURE symbolic proof
    via structural lemmas + Bool case analysis on 4 atoms.

    Statement:
      deltaList 2 (cupList 1 1 α β) τ
      = (cupList 2 1 (deltaList 1 α) β τ)
        ⊕ (cupList 1 2 α (deltaList 1 β) τ)
        ⊕ (cupList 1 1 α β (τ.eraseIdx 1))

    Proof strategy: unfold both sides into expressions in 4 Bool
    atoms (α at three different lists, β at three different lists)
    using `LeibnizLexStructural.*` commutation lemmas; verify
    equality by `cases` on each atom.  PURE. -/
theorem list_level_leibniz_1_1 (α β : List Nat → Bool) (τ : List Nat) :
    deltaList 2 (cupList 1 1 α β) τ
    = xor (xor (cupList 2 1 (deltaList 1 α) β τ)
               (cupList 1 2 α (deltaList 1 β) τ))
          (cupList 1 1 α β (τ.eraseIdx 1)) := by
  -- Apply structural lemmas to each face's cupList.
  -- For i = 0 (i < k = 1):
  have e0_take : (τ.eraseIdx 0).take 1 = (τ.take 2).eraseIdx 0 :=
    eraseIdx_take_low τ 0 1 (Nat.zero_le 1)
  have e0_drop : (τ.eraseIdx 0).drop 1 = τ.drop 2 := by
    cases τ <;> rfl
  -- For i = 1 (= k):
  have e1_take : (τ.eraseIdx 1).take 1 = τ.take 1 :=
    eraseIdx_take_boundary τ 1
  have e1_drop : (τ.eraseIdx 1).drop 1 = τ.drop 2 :=
    eraseIdx_drop_boundary τ 1
  -- For i = 2 (i > k, = k + 0 + 1):
  have e2_take : (τ.eraseIdx 2).take 1 = τ.take 1 :=
    eraseIdx_take_high τ 1 0
  have e2_drop : (τ.eraseIdx 2).drop 1 = (τ.drop 1).eraseIdx 1 :=
    eraseIdx_drop_high τ 1 0
  -- Bring (τ.take 2).eraseIdx 1 = τ.take 1 (used in (δα ⌣ β) unfold):
  have take2_e1 : (τ.take 2).eraseIdx 1 = τ.take 1 := by
    cases τ with
    | nil => rfl
    | cons x xs =>
      show ((x :: xs).take 2).eraseIdx 1 = (x :: xs).take 1
      cases xs with
      | nil => rfl
      | cons y ys => rfl
  -- Bring (τ.drop 1).eraseIdx 0 = τ.drop 2 (used in (α ⌣ δβ) unfold):
  have drop1_e0 : (τ.drop 1).eraseIdx 0 = τ.drop 2 := by
    cases τ with
    | nil => rfl
    | cons _ xs =>
      cases xs <;> rfl
  -- Unfold cupList and deltaList; substitute the lemmas
  unfold cupList deltaList
  show xor (xor (xor false
              (α ((τ.eraseIdx 0).take 1) && β ((τ.eraseIdx 0).drop 1)))
              (α ((τ.eraseIdx 1).take 1) && β ((τ.eraseIdx 1).drop 1)))
            (α ((τ.eraseIdx 2).take 1) && β ((τ.eraseIdx 2).drop 1))
       = xor (xor
             ((xor (xor false (α ((τ.take 2).eraseIdx 0)))
                                (α ((τ.take 2).eraseIdx 1))) && β (τ.drop 2))
             (α (τ.take 1) && (xor (xor false (β ((τ.drop 1).eraseIdx 0)))
                                     (β ((τ.drop 1).eraseIdx 1)))))
           (α ((τ.eraseIdx 1).take 1) && β ((τ.eraseIdx 1).drop 1))
  rw [e0_take, e0_drop, e1_take, e1_drop, e2_take, e2_drop,
      take2_e1, drop1_e0]
  -- Goal now in terms of 4 atoms.  Verify by case analysis on each.
  cases h1 : α ((τ.take 2).eraseIdx 0) <;>
  cases h2 : α (τ.take 1) <;>
  cases h3 : β (τ.drop 2) <;>
  cases h4 : β ((τ.drop 1).eraseIdx 1) <;> rfl

/-! ## §6.  List-level (2, 1) twisted Leibniz — symbolic proof

Confirms the **list-level** proof strategy generalises to different
bidegrees.  Same structure as §5: structural lemmas + Bool case
analysis on 5 atoms (A30, A31, A2, B3, Bx). -/

/-- ★★★ **List-level (2, 1) twisted Leibniz** — PURE symbolic proof.

    Statement (k=2, l=1; τ a list of length k+l+1 = 4 in semantic
    use, but the theorem holds for any τ since structural lemmas
    handle nil/short list cases gracefully):

      deltaList 3 (cupList 2 1 α β) τ
      = (cupList 3 1 (deltaList 2 α) β τ)
        ⊕ (cupList 2 2 α (deltaList 1 β) τ)
        ⊕ (cupList 2 1 α β (τ.eraseIdx 2))

    PURE. -/
theorem list_level_leibniz_2_1 (α β : List Nat → Bool) (τ : List Nat) :
    deltaList 3 (cupList 2 1 α β) τ
    = xor (xor (cupList 3 1 (deltaList 2 α) β τ)
               (cupList 2 2 α (deltaList 1 β) τ))
          (cupList 2 1 α β (τ.eraseIdx 2)) := by
  -- Structural lemmas at each face.
  -- For i = 0 (i < k = 2):
  have e0_take : (τ.eraseIdx 0).take 2 = (τ.take 3).eraseIdx 0 :=
    eraseIdx_take_low τ 0 2 (Nat.zero_le 2)
  have e0_drop : (τ.eraseIdx 0).drop 2 = τ.drop 3 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs with
      | nil => rfl
      | cons _ ys => rfl
  -- For i = 1 (i < k = 2):
  have e1_take : (τ.eraseIdx 1).take 2 = (τ.take 3).eraseIdx 1 :=
    eraseIdx_take_low τ 1 2 (by decide)
  have e1_drop : (τ.eraseIdx 1).drop 2 = τ.drop 3 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs with
      | nil => rfl
      | cons _ ys => rfl
  -- For i = 2 (= k):
  have e2_take : (τ.eraseIdx 2).take 2 = τ.take 2 :=
    eraseIdx_take_boundary τ 2
  have e2_drop : (τ.eraseIdx 2).drop 2 = τ.drop 3 :=
    eraseIdx_drop_boundary τ 2
  -- For i = 3 (i > k, = k + 0 + 1):
  have e3_take : (τ.eraseIdx 3).take 2 = τ.take 2 :=
    eraseIdx_take_high τ 2 0
  have e3_drop : (τ.eraseIdx 3).drop 2 = (τ.drop 2).eraseIdx 1 :=
    eraseIdx_drop_high τ 2 0
  -- (τ.take 3).eraseIdx 2 = τ.take 2 (last element of take 3 is τ[2]):
  have take3_e2 : (τ.take 3).eraseIdx 2 = τ.take 2 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs with
      | nil => rfl
      | cons _ ys => cases ys with
        | nil => rfl
        | cons _ zs => rfl
  -- (τ.drop 2).eraseIdx 0 = τ.drop 3 (first element of drop 2 is τ[2]):
  have drop2_e0 : (τ.drop 2).eraseIdx 0 = τ.drop 3 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs with
      | nil => rfl
      | cons _ ys => cases ys <;> rfl
  unfold cupList deltaList
  show xor (xor (xor (xor false
            (α ((τ.eraseIdx 0).take 2) && β ((τ.eraseIdx 0).drop 2)))
            (α ((τ.eraseIdx 1).take 2) && β ((τ.eraseIdx 1).drop 2)))
            (α ((τ.eraseIdx 2).take 2) && β ((τ.eraseIdx 2).drop 2)))
           (α ((τ.eraseIdx 3).take 2) && β ((τ.eraseIdx 3).drop 2))
       = xor (xor
             ((xor (xor (xor false (α ((τ.take 3).eraseIdx 0)))
                                     (α ((τ.take 3).eraseIdx 1)))
                                     (α ((τ.take 3).eraseIdx 2))) && β (τ.drop 3))
             (α (τ.take 2) && (xor (xor false (β ((τ.drop 2).eraseIdx 0)))
                                     (β ((τ.drop 2).eraseIdx 1)))))
           (α ((τ.eraseIdx 2).take 2) && β ((τ.eraseIdx 2).drop 2))
  rw [e0_take, e0_drop, e1_take, e1_drop, e2_take, e2_drop, e3_take, e3_drop,
      take3_e2, drop2_e0]
  -- 5 atoms: A30, A31, A2, B3, Bx
  cases α ((τ.take 3).eraseIdx 0) <;>
  cases α ((τ.take 3).eraseIdx 1) <;>
  cases α (τ.take 2) <;>
  cases β (τ.drop 3) <;>
  cases β ((τ.drop 2).eraseIdx 1) <;> rfl

/-! ## §7.  List-level (1, 2) twisted Leibniz — symmetric to (2, 1)

By the symmetry of the lex-projection cup's role, the (1, 2)
case mirrors (2, 1) with α and β roles structurally swapped.
Proven with the same structural lemma toolkit. -/

/-- ★★★ **List-level (1, 2) twisted Leibniz** — PURE symbolic.

    Statement (k=1, l=2; correction at position k=1):

      deltaList 3 (cupList 1 2 α β) τ
      = (cupList 2 2 (deltaList 1 α) β τ)
        ⊕ (cupList 1 3 α (deltaList 2 β) τ)
        ⊕ (cupList 1 2 α β (τ.eraseIdx 1))

    PURE.  -/
theorem list_level_leibniz_1_2 (α β : List Nat → Bool) (τ : List Nat) :
    deltaList 3 (cupList 1 2 α β) τ
    = xor (xor (cupList 2 2 (deltaList 1 α) β τ)
               (cupList 1 3 α (deltaList 2 β) τ))
          (cupList 1 2 α β (τ.eraseIdx 1)) := by
  -- Face structural decomposition: τ has length k+l+1 = 4 in
  -- semantic use; with k=1, the boundary face is at position 1.
  -- For i = 0 (i < k = 1):
  have e0_take : (τ.eraseIdx 0).take 1 = (τ.take 2).eraseIdx 0 :=
    eraseIdx_take_low τ 0 1 (Nat.zero_le 1)
  have e0_drop : (τ.eraseIdx 0).drop 1 = τ.drop 2 := by
    cases τ <;> rfl
  -- For i = 1 (= k):
  have e1_take : (τ.eraseIdx 1).take 1 = τ.take 1 :=
    eraseIdx_take_boundary τ 1
  have e1_drop : (τ.eraseIdx 1).drop 1 = τ.drop 2 :=
    eraseIdx_drop_boundary τ 1
  -- For i = 2 (i > k, = k + 0 + 1):
  have e2_take : (τ.eraseIdx 2).take 1 = τ.take 1 :=
    eraseIdx_take_high τ 1 0
  have e2_drop : (τ.eraseIdx 2).drop 1 = (τ.drop 1).eraseIdx 1 :=
    eraseIdx_drop_high τ 1 0
  -- For i = 3 (i > k, = k + 1 + 1):
  have e3_take : (τ.eraseIdx 3).take 1 = τ.take 1 :=
    eraseIdx_take_high τ 1 1
  have e3_drop : (τ.eraseIdx 3).drop 1 = (τ.drop 1).eraseIdx 2 :=
    eraseIdx_drop_high τ 1 1
  -- (τ.take 2).eraseIdx 1 = τ.take 1
  have take2_e1 : (τ.take 2).eraseIdx 1 = τ.take 1 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs <;> rfl
  -- (τ.drop 1).eraseIdx 0 = τ.drop 2
  have drop1_e0 : (τ.drop 1).eraseIdx 0 = τ.drop 2 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs <;> rfl
  unfold cupList deltaList
  show xor (xor (xor (xor false
            (α ((τ.eraseIdx 0).take 1) && β ((τ.eraseIdx 0).drop 1)))
            (α ((τ.eraseIdx 1).take 1) && β ((τ.eraseIdx 1).drop 1)))
            (α ((τ.eraseIdx 2).take 1) && β ((τ.eraseIdx 2).drop 1)))
           (α ((τ.eraseIdx 3).take 1) && β ((τ.eraseIdx 3).drop 1))
       = xor (xor
             ((xor (xor false (α ((τ.take 2).eraseIdx 0)))
                     (α ((τ.take 2).eraseIdx 1))) && β (τ.drop 2))
             (α (τ.take 1) && (xor (xor (xor false (β ((τ.drop 1).eraseIdx 0)))
                                          (β ((τ.drop 1).eraseIdx 1)))
                                          (β ((τ.drop 1).eraseIdx 2)))))
           (α ((τ.eraseIdx 1).take 1) && β ((τ.eraseIdx 1).drop 1))
  rw [e0_take, e0_drop, e1_take, e1_drop, e2_take, e2_drop,
      e3_take, e3_drop, take2_e1, drop1_e0]
  -- 5 atoms: α((τ.take 2).eraseIdx 0), α(τ.take 1), β(τ.drop 2),
  --          β((τ.drop 1).eraseIdx 1), β((τ.drop 1).eraseIdx 2)
  cases α ((τ.take 2).eraseIdx 0) <;>
  cases α (τ.take 1) <;>
  cases β (τ.drop 2) <;>
  cases β ((τ.drop 1).eraseIdx 1) <;>
  cases β ((τ.drop 1).eraseIdx 2) <;> rfl

/-! ## §8.  List-level (2, 2) twisted Leibniz

Both bidegree components equal — 4-th bidegree confirmed via the
same 3-way partition strategy.  6 atoms (3 α + 3 β). -/

/-- ★★★ **List-level (2, 2) twisted Leibniz** — PURE symbolic.

    Statement (k=2, l=2; τ length k+l+1 = 5 in semantic use):

      deltaList 4 (cupList 2 2 α β) τ
      = (cupList 3 2 (deltaList 2 α) β τ)
        ⊕ (cupList 2 3 α (deltaList 2 β) τ)
        ⊕ (cupList 2 2 α β (τ.eraseIdx 2))

    PURE.  -/
theorem list_level_leibniz_2_2 (α β : List Nat → Bool) (τ : List Nat) :
    deltaList 4 (cupList 2 2 α β) τ
    = xor (xor (cupList 3 2 (deltaList 2 α) β τ)
               (cupList 2 3 α (deltaList 2 β) τ))
          (cupList 2 2 α β (τ.eraseIdx 2)) := by
  -- Face decomposition: 5 faces at i = 0..4
  -- For i = 0 (i < k = 2):
  have e0_take : (τ.eraseIdx 0).take 2 = (τ.take 3).eraseIdx 0 :=
    eraseIdx_take_low τ 0 2 (Nat.zero_le 2)
  have e0_drop : (τ.eraseIdx 0).drop 2 = τ.drop 3 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs <;> rfl
  -- For i = 1 (i < k = 2):
  have e1_take : (τ.eraseIdx 1).take 2 = (τ.take 3).eraseIdx 1 :=
    eraseIdx_take_low τ 1 2 (by decide)
  have e1_drop : (τ.eraseIdx 1).drop 2 = τ.drop 3 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs <;> rfl
  -- For i = 2 (= k):
  have e2_take : (τ.eraseIdx 2).take 2 = τ.take 2 :=
    eraseIdx_take_boundary τ 2
  have e2_drop : (τ.eraseIdx 2).drop 2 = τ.drop 3 :=
    eraseIdx_drop_boundary τ 2
  -- For i = 3 (i > k, = k + 0 + 1):
  have e3_take : (τ.eraseIdx 3).take 2 = τ.take 2 :=
    eraseIdx_take_high τ 2 0
  have e3_drop : (τ.eraseIdx 3).drop 2 = (τ.drop 2).eraseIdx 1 :=
    eraseIdx_drop_high τ 2 0
  -- For i = 4 (i > k, = k + 1 + 1):
  have e4_take : (τ.eraseIdx 4).take 2 = τ.take 2 :=
    eraseIdx_take_high τ 2 1
  have e4_drop : (τ.eraseIdx 4).drop 2 = (τ.drop 2).eraseIdx 2 :=
    eraseIdx_drop_high τ 2 1
  -- (τ.take 3).eraseIdx 2 = τ.take 2
  have take3_e2 : (τ.take 3).eraseIdx 2 = τ.take 2 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs with
      | nil => rfl
      | cons _ ys => cases ys <;> rfl
  -- (τ.drop 2).eraseIdx 0 = τ.drop 3
  have drop2_e0 : (τ.drop 2).eraseIdx 0 = τ.drop 3 := by
    cases τ with
    | nil => rfl
    | cons _ xs => cases xs with
      | nil => rfl
      | cons _ ys => cases ys <;> rfl
  unfold cupList deltaList
  show xor (xor (xor (xor (xor false
            (α ((τ.eraseIdx 0).take 2) && β ((τ.eraseIdx 0).drop 2)))
            (α ((τ.eraseIdx 1).take 2) && β ((τ.eraseIdx 1).drop 2)))
            (α ((τ.eraseIdx 2).take 2) && β ((τ.eraseIdx 2).drop 2)))
            (α ((τ.eraseIdx 3).take 2) && β ((τ.eraseIdx 3).drop 2)))
           (α ((τ.eraseIdx 4).take 2) && β ((τ.eraseIdx 4).drop 2))
       = xor (xor
             ((xor (xor (xor false (α ((τ.take 3).eraseIdx 0)))
                                     (α ((τ.take 3).eraseIdx 1)))
                                     (α ((τ.take 3).eraseIdx 2))) && β (τ.drop 3))
             (α (τ.take 2) && (xor (xor (xor false (β ((τ.drop 2).eraseIdx 0)))
                                          (β ((τ.drop 2).eraseIdx 1)))
                                          (β ((τ.drop 2).eraseIdx 2)))))
           (α ((τ.eraseIdx 2).take 2) && β ((τ.eraseIdx 2).drop 2))
  rw [e0_take, e0_drop, e1_take, e1_drop, e2_take, e2_drop,
      e3_take, e3_drop, e4_take, e4_drop, take3_e2, drop2_e0]
  -- 6 atoms total
  cases α ((τ.take 3).eraseIdx 0) <;>
  cases α ((τ.take 3).eraseIdx 1) <;>
  cases α (τ.take 2) <;>
  cases β (τ.drop 3) <;>
  cases β ((τ.drop 2).eraseIdx 1) <;>
  cases β ((τ.drop 2).eraseIdx 2) <;> rfl

/-! ## §9.  Custom range fold (avoids [propext] via List.range_succ)

`List.range_succ` in Lean core introduces `[propext]`.  To keep
strict-PURE infrastructure for general (k, l) symbolic proofs, we
define a custom `xorRange` operator with clean structural
recursion. -/

/-- ★ **Custom XOR fold over Nat range [0..n-1]**.
    Structural recursion; admits clean split lemmas without
    depending on `List.range_succ` (which is [propext]). -/
def xorRange : Nat → (Nat → Bool) → Bool
  | 0,     _ => false
  | n + 1, f => xor (xorRange n f) (f n)

/-- ★ XOR associativity on Bool. -/
theorem xor_assoc' (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- ★★★ **xorRange split-at-position** — the key lemma for ∀(k, l)
    symbolic proofs.  At position k, the XOR over [0..k+l] splits
    cleanly into [0..k-1] ⊕ {k} ⊕ [k+1..k+l] (with the third block
    reindexed via `(· + k + 1)`).  PURE. -/
theorem xorRange_split (k l : Nat) (f : Nat → Bool) :
    xorRange (k + l + 1) f
    = xor (xor (xorRange k f) (f k))
          (xorRange l (fun j => f (k + j + 1))) := by
  induction l with
  | zero =>
    -- xorRange (k+0+1) f = xorRange (k+1) f = xor (xorRange k f) (f k)
    -- RHS = xor (xor (xorRange k f) (f k)) (xorRange 0 _)
    --     = xor (xor (xorRange k f) (f k)) false
    show xor (xorRange k f) (f k)
       = xor (xor (xorRange k f) (f k)) false
    cases (xor (xorRange k f) (f k)) <;> rfl
  | succ l' ih =>
    -- xorRange (k+(l'+1)+1) f = xorRange (k+l'+2) f
    --                        = xor (xorRange (k+l'+1) f) (f (k+l'+1))
    -- RHS = xor (xor (xorRange k f) (f k)) (xorRange (l'+1) (fun j => ...))
    --     = xor (xor (xorRange k f) (f k))
    --           (xor (xorRange l' (fun j => f(k+j+1))) (f (k+l'+1)))
    -- Apply IH + associativity
    have hk : k + (l' + 1) + 1 = (k + l' + 1) + 1 := rfl
    rw [hk]
    show xor (xorRange (k + l' + 1) f) (f (k + l' + 1))
       = xor (xor (xorRange k f) (f k))
             (xor (xorRange l' (fun j => f (k + j + 1)))
                  (f (k + l' + 1)))
    rw [ih]
    -- xor (xor X Y) Z = xor X (xor Y Z) via xor_assoc'
    exact xor_assoc' _ _ _

/-! ## §10.  xorRange ↔ AND distribution lemmas

For the cup-level general-(k,l) assembly, we need both left- and
right-AND distribution over xorRange.  Plus a refactored
`deltaListR` using xorRange. -/

/-- ★ **Left AND distributes over xorRange**.  PURE. -/
theorem and_distrib_xorRange_left (c : Bool) (f : Nat → Bool) (n : Nat) :
    (c && xorRange n f) = xorRange n (fun i => c && f i) := by
  induction n with
  | zero => show (c && false) = false; cases c <;> rfl
  | succ k ih =>
    show (c && xor (xorRange k f) (f k))
       = xor (xorRange k (fun i => c && f i)) (c && f k)
    rw [and_xor_distrib_left, ih]

/-- ★ **AND-XOR right distributivity**: (a ⊕ b) && c = (a && c) ⊕ (b && c). -/
theorem and_xor_distrib_right (a b c : Bool) :
    (xor a b && c) = xor (a && c) (b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- ★ **Right AND distributes over xorRange**.  PURE. -/
theorem and_distrib_xorRange_right (c : Bool) (f : Nat → Bool) (n : Nat) :
    (xorRange n f && c) = xorRange n (fun i => f i && c) := by
  induction n with
  | zero => show (false && c) = false; cases c <;> rfl
  | succ k ih =>
    show (xor (xorRange k f) (f k) && c)
       = xor (xorRange k (fun i => f i && c)) (f k && c)
    rw [and_xor_distrib_right, ih]

/-- Custom xorRange-based deltaList for the structural ∀(k,l) form.
    Equivalent to deltaList but uses xorRange to avoid List.range
    [propext] dependency. -/
def deltaListR (k : Nat) (σ : List Nat → Bool) (τ : List Nat) : Bool :=
  xorRange (k + 1) (fun i => σ (τ.eraseIdx i))

/-! ## §11.  xorRange congruence and generic 3-way partition

xorRange respects pointwise equality of its argument function;
combining with `xorRange_split` yields a *generic* algebraic 3-way
partition decomposition usable as the algebraic skeleton of any
cup-level (k, l) symbolic proof. -/

/-- ★ **xorRange respects pointwise equality** on its domain
    [0..n-1].  PURE. -/
theorem xorRange_congr (n : Nat) (f g : Nat → Bool)
    (h : ∀ i, i < n → f i = g i) :
    xorRange n f = xorRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show xor (xorRange k f) (f k) = xor (xorRange k g) (g k)
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    rw [h k (Nat.lt_succ_self k)]

/-- ★★★ **Generic 3-way XOR partition** — abstract algebraic
    skeleton of the lex-projection cup Leibniz, parameterised by
    arbitrary face-value functions for each of the three blocks.

    Statement: if `f` decomposes case-wise on the partition
    `[0..k-1] / {k} / [k+1..k+l]` as block sequences `g_lt`,
    `g_eq`, `g_gt`, then the XOR sum factors:

      xorRange (k+l+1) f
      = (xorRange k g_lt) ⊕ g_eq ⊕ (xorRange l g_gt)

    This is the **pure algebraic content** of the user's 3-way
    partition strategy.  PURE. -/
theorem xorRange_three_way_partition (k l : Nat) (f : Nat → Bool)
    (g_lt : Nat → Bool) (g_eq : Bool) (g_gt : Nat → Bool)
    (h_lt : ∀ i, i < k → f i = g_lt i)
    (h_eq : f k = g_eq)
    (h_gt : ∀ j, j < l → f (k + j + 1) = g_gt j) :
    xorRange (k + l + 1) f
    = xor (xor (xorRange k g_lt) g_eq) (xorRange l g_gt) := by
  -- Apply xorRange_split at position k
  rw [xorRange_split k l f]
  -- Three blocks:
  --   xorRange k f      = xorRange k g_lt  (by xorRange_congr)
  --   f k              = g_eq             (by h_eq)
  --   xorRange l (fun j => f (k+j+1)) = xorRange l g_gt (by congr)
  rw [xorRange_congr k f g_lt h_lt]
  rw [h_eq]
  rw [xorRange_congr l (fun j => f (k + j + 1)) g_gt h_gt]

/-! ## §12.  Cup-level face-decomposition + LHS partition (PURE)

`cupList_face_decomp` discharges the three structural hypotheses
of `xorRange_three_way_partition` for the lex-projection cup at
arbitrary (k, l) bidegree.  This composes with the generic 3-way
partition to yield the explicit LHS expansion for ∀ (k, l). -/

/-- Auxiliary: drop low — for i < k, `(l.eraseIdx i).drop k = l.drop (k+1)`.
    Companion to `LeibnizLexStructural.eraseIdx_take_low`.  PURE. -/
theorem eraseIdx_drop_low {α} (l : List α) :
    ∀ (i k : Nat), i ≤ k →
      (l.eraseIdx i).drop k = l.drop (k + 1) := by
  induction l with
  | nil => intro i k _; cases k <;> rfl
  | cons x xs ih =>
    intro i k hik
    cases i with
    | zero =>
      cases k with
      | zero => rfl
      | succ _ => rfl
    | succ i' =>
      cases k with
      | zero => exact absurd hik (Nat.not_succ_le_zero i')
      | succ k' =>
        show (x :: xs.eraseIdx i').drop (k' + 1)
             = (x :: xs).drop (k' + 1 + 1)
        rw [List.drop]
        have hi' : i' ≤ k' := Nat.le_of_succ_le_succ hik
        exact ih i' k' hi'

/-- ★★★ **Cup-level face decomposition** at arbitrary (k, l).

    The lex-projection cup at any face `τ.eraseIdx i` of the
    (k+l+1)-list τ decomposes into one of three structural forms
    depending on whether `i < k`, `i = k`, or `i > k`.  Discharges
    all three structural hypotheses of `xorRange_three_way_partition`.
    PURE. -/
theorem cupList_face_decomp (k l : Nat)
    (α β : List Nat → Bool) (τ : List Nat) :
    (∀ i, i < k →
      cupList k l α β (τ.eraseIdx i)
      = (α ((τ.take (k+1)).eraseIdx i) && β (τ.drop (k+1))))
    ∧ (cupList k l α β (τ.eraseIdx k)
       = (α (τ.take k) && β (τ.drop (k+1))))
    ∧ (∀ j, j < l →
      cupList k l α β (τ.eraseIdx (k + j + 1))
      = (α (τ.take k) && β ((τ.drop k).eraseIdx (j+1)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    unfold cupList
    rw [eraseIdx_take_low τ i k (Nat.le_of_lt hi)]
    rw [eraseIdx_drop_low τ i k (Nat.le_of_lt hi)]
  · unfold cupList
    rw [eraseIdx_take_boundary τ k, eraseIdx_drop_boundary τ k]
  · intro j _hj
    unfold cupList
    rw [eraseIdx_take_high τ k j, eraseIdx_drop_high τ k j]

/-- ★★★★★ **General ∀(k,l) LHS partition** — the complete
    symbolic decomposition of `xorRange (k+l+1) (face cupList)`
    into three blocks at arbitrary bidegree.

    Statement:
      xorRange (k+l+1) (fun i => cupList k l α β (τ.eraseIdx i))
      = (Block 1: xorRange k of α-on-take · β-on-drop)
        ⊕ (correction = α(τ.take k) · β(τ.drop(k+1)))
        ⊕ (Block 3: xorRange l of α-on-take · β-on-drop-erased)

    Composes `xorRange_three_way_partition` with `cupList_face_decomp`.
    This is the **algebraic skeleton** of the lex-projection cup's
    Leibniz at arbitrary (k, l).  PURE.  ∀ α β τ. -/
theorem list_level_LHS_partition (k l : Nat)
    (α β : List Nat → Bool) (τ : List Nat) :
    xorRange (k + l + 1) (fun i => cupList k l α β (τ.eraseIdx i))
    = xor (xor
            (xorRange k (fun i =>
              α ((τ.take (k+1)).eraseIdx i) && β (τ.drop (k+1))))
            (α (τ.take k) && β (τ.drop (k+1))))
          (xorRange l (fun j =>
              α (τ.take k) && β ((τ.drop k).eraseIdx (j+1)))) := by
  have ⟨h_lt, h_eq, h_gt⟩ := cupList_face_decomp k l α β τ
  exact xorRange_three_way_partition k l _ _ _ _ h_lt h_eq h_gt

/-! ## §13.  Bridging LHS partition → standard Leibniz form (PURE)

Composing `list_level_LHS_partition` with XOR algebra identities
yields the **full ∀(k,l) symbolic twisted Leibniz** at the list
level.  The bridge: each LHS block sum (xorRange k of face_1_func,
xorRange l of face_3_func) relates to a cupList of (deltaListR ·)
via xorRange (k+1)/(l+1) unfolds + correction cancellation. -/

/-- Auxiliary: `xor a a = false`.  -/
theorem xor_self' (a : Bool) : xor a a = false := by cases a <;> rfl

/-- (τ.drop k).eraseIdx 0 = τ.drop (k+1) (boundary). -/
theorem drop_eraseIdx_zero {α} (l : List α) (k : Nat) :
    (l.drop k).eraseIdx 0 = l.drop (k + 1) := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons _ xs ih =>
    cases k with
    | zero => rfl
    | succ k' => exact ih k'

/-- (τ.take (k+1)).eraseIdx k = τ.take k (boundary). -/
theorem take_succ_eraseIdx {α} (l : List α) (k : Nat) :
    (l.take (k + 1)).eraseIdx k = l.take k := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons _ xs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      show ((xs.take (k' + 1)).eraseIdx k' : List _).cons _ = _
      simp only [List.take, List.eraseIdx]
      exact congrArg _ (ih k')

/-- ★★★★★★ **General ∀(k,l) twisted Leibniz** at the list level —
    THE main result.

    For arbitrary `α β : List Nat → Bool`, `τ : List Nat`, and any
    bidegree `(k, l : Nat)`:

      xorRange (k+l+1) (fun i => cupList k l α β (τ.eraseIdx i))
      = xor (xor (cupList (k+1) l (deltaListR k α) β τ)
                 (cupList k (l+1) α (deltaListR l β) τ))
            (cupList k l α β (τ.eraseIdx k))

    The proof composes:
      · `list_level_LHS_partition` (LHS → 3-block form)
      · cupList/deltaListR unfolds via and_distrib_xorRange_left/right
      · xorRange (n+1) = xor (xorRange n) (· n) at the boundary
      · take/drop boundary lemmas (take_succ_eraseIdx, drop_eraseIdx_zero)
      · xor_self' + xor_assoc' XOR algebra to cancel duplicate corrections

    Closes the user's 3-way partition strategy for ALL (k, l) at
    the list level.  PURE.  ∀ α β τ. -/
theorem list_level_leibniz_general (k l : Nat)
    (α β : List Nat → Bool) (τ : List Nat) :
    xorRange (k + l + 1) (fun i => cupList k l α β (τ.eraseIdx i))
    = xor (xor (cupList (k+1) l (deltaListR k α) β τ)
               (cupList k (l+1) α (deltaListR l β) τ))
          (cupList k l α β (τ.eraseIdx k)) := by
  -- Step 1: apply list_level_LHS_partition
  rw [list_level_LHS_partition k l α β τ]
  -- Step 2: relate LHS expressions to cupList of (deltaListR ·)
  -- Block 1 expression:
  --   xorRange k (fun i => α((τ.take(k+1)).eraseIdx i) && β(τ.drop(k+1)))
  -- = (xorRange k of (fun i => α((τ.take(k+1)).eraseIdx i))) && β(τ.drop(k+1))
  rw [← and_distrib_xorRange_right (β (τ.drop (k+1)))
        (fun i => α ((τ.take (k+1)).eraseIdx i)) k]
  -- Block 3 expression:
  --   xorRange l (fun j => α(τ.take k) && β((τ.drop k).eraseIdx (j+1)))
  -- = α(τ.take k) && (xorRange l of (fun j => β((τ.drop k).eraseIdx (j+1))))
  rw [← and_distrib_xorRange_left (α (τ.take k))
        (fun j => β ((τ.drop k).eraseIdx (j+1))) l]
  -- Step 3: unfold the RHS cup/delta operations
  unfold cupList deltaListR
  -- RHS Block 1: (xorRange (k+1) (i => α((τ.take(k+1)).eraseIdx i))) && β(τ.drop(k+1))
  --           = (xor (xorRange k _) (α((τ.take(k+1)).eraseIdx k))) && β(τ.drop(k+1))
  --           = xor ((xorRange k _) && β(τ.drop(k+1))) ((α((τ.take(k+1)).eraseIdx k)) && β(τ.drop(k+1)))
  --           = xor (Block1 sum) ((α((τ.take(k+1)).eraseIdx k)) && β(τ.drop(k+1)))
  -- By take_succ_eraseIdx: (τ.take(k+1)).eraseIdx k = τ.take k
  -- So RHS Block 1 = xor (Block1 sum) (α(τ.take k) && β(τ.drop(k+1)))
  --              = xor (Block1 sum) correction
  show xor (xor ((xorRange k (fun i => α ((τ.take (k+1)).eraseIdx i)))
                  && β (τ.drop (k+1)))
                ((α (τ.take k)) && β (τ.drop (k+1))))
            ((α (τ.take k)) && (xorRange l (fun j =>
                  β ((τ.drop k).eraseIdx (j+1)))))
       = xor (xor ((xorRange (k+1) (fun i => α ((τ.take (k+1)).eraseIdx i)))
                    && β (τ.drop (k+1)))
                  ((α (τ.take k)) && (xorRange (l+1) (fun j =>
                    β ((τ.drop k).eraseIdx j)))))
              ((α ((τ.eraseIdx k).take k)) && β ((τ.eraseIdx k).drop k))
  rw [eraseIdx_take_boundary τ k, eraseIdx_drop_boundary τ k]
  -- Helper: unfold the xorRange (k+1) ↔ xorRange k + boundary
  have unfold_R1 :
      xorRange (k+1) (fun i => α ((τ.take (k+1)).eraseIdx i))
      = xor (xorRange k (fun i => α ((τ.take (k+1)).eraseIdx i)))
            (α (τ.take k)) := by
    show xor (xorRange k _) (α ((τ.take (k+1)).eraseIdx k))
       = xor (xorRange k _) (α (τ.take k))
    rw [take_succ_eraseIdx]
  -- Helper: unfold the xorRange (l+1) ↔ boundary + reindexed xorRange l
  have hzla : 0 + l + 1 = l + 1 := by rw [Nat.zero_add]
  have unfold_R2 :
      xorRange (l+1) (fun j => β ((τ.drop k).eraseIdx j))
      = xor (β (τ.drop (k+1)))
            (xorRange l (fun j => β ((τ.drop k).eraseIdx (j+1)))) := by
    have := xorRange_split 0 l (fun j => β ((τ.drop k).eraseIdx j))
    -- this : xorRange (0+l+1) ... = xor (xor (xorRange 0 _) (_ 0)) (xorRange l _shift)
    rw [hzla] at this
    rw [this]
    show xor (xor false (β ((τ.drop k).eraseIdx 0)))
             (xorRange l (fun j => β ((τ.drop k).eraseIdx (0 + j + 1))))
         = xor (β (τ.drop (k+1)))
             (xorRange l (fun j => β ((τ.drop k).eraseIdx (j+1))))
    rw [drop_eraseIdx_zero τ k]
    -- xor false x = x; reindex 0+j+1 = j+1 via xorRange_congr (no funext)
    have hreindex : xorRange l (fun j => β ((τ.drop k).eraseIdx (0 + j + 1)))
                  = xorRange l (fun j => β ((τ.drop k).eraseIdx (j + 1))) := by
      apply xorRange_congr
      intro j _
      rw [Nat.zero_add]
    rw [hreindex]
    cases β (τ.drop (k+1)) <;> rfl
  rw [unfold_R1, and_xor_distrib_right, unfold_R2, and_xor_distrib_left]
  -- Goal now: pure XOR algebra.
  -- LHS form: xor (xor (B1 && β_drop) corr) (α_take && B3_sum)
  --   where B1 = xorRange k _, B3_sum = xorRange l _, corr = α_take && β_drop
  -- RHS form: xor (xor (xor (B1 && β_drop) (α_take && β_drop))
  --                    (xor (α_take && β_drop) (α_take && B3_sum)))
  --               corr
  --         where corr = α_take && β_drop (after boundary rewrites)
  -- = xor (xor (B1_dist ⊕ corr) (corr ⊕ B3_dist)) corr
  --   where B1_dist = B1 && β_drop, B3_dist = α_take && B3_sum
  -- Apply xor_assoc' + xor_self' to cancel doubled corr terms.
  -- After algebra: LHS = xor (xor B1_dist corr) B3_dist
  --              RHS = xor (xor B1_dist (xor corr corr)) (xor B3_dist corr) ⊕ corr  -- simplify
  -- Both reduce to: xor (xor B1_dist corr) B3_dist
  -- (modulo XOR commutativity which is delicate; use Bool case analysis if needed)
  -- The Bool case analysis on 4 atoms (B1_dist, B3_dist, α_take && β_drop, β_drop)
  -- closes the goal.
  cases hX : xorRange k (fun i => α ((τ.take (k+1)).eraseIdx i)) <;>
  cases hY : xorRange l (fun j => β ((τ.drop k).eraseIdx (j+1))) <;>
  cases hα : α (τ.take k) <;>
  cases hβ : β (τ.drop (k+1)) <;> rfl

end E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel
