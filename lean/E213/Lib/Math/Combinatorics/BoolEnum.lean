import E213.Meta.Tactic.List213

/-!
# Finite Bool-cardinality enumeration (∅-axiom)

Mathlib-free core Lean has no `Fintype` / `Finset.card`, and its `List`
membership / `Nodup` lemmas carry `propext`.  So a strict-∅-axiom
finite-cardinality argument over `Bool`-valued data needs the
enumeration built by hand.

This file enumerates **all length-`n` `Bool` lists** — the ∅-axiom stand-in
for "all functions `Fin n → Bool`", with `List Bool` chosen over
`Fin n → Bool` precisely so equality is decidable list equality (no
`funext`) and the count is `List.length` (no `Fintype`):

  - `allBoolLists n` — the `2^n` length-`n` Bool lists;
  - `allBoolLists_length` — `|allBoolLists n| = 2^n`;
  - `mem_allBoolLists` — completeness: every length-`n` list is listed;
  - `allBoolLists_nodup` — no duplicates.

Together these make `allBoolLists n` a finite carrier of exact, ∅-axiom
cardinality `2^n` — the base for counting Bool-cochain subsets (e.g. the
δ⁰-kernel) without `decide`-per-instance.

Companion: `theory/math/combinatorics/bool_enumeration.md`.
-/

namespace E213.Lib.Math.Combinatorics.BoolEnum

open E213.Tactic.List213 (length_append length_map mem_map_of_mem exists_of_mem_map
  mem_append_left mem_append_right mem_append_iff nodup_append nodup_map_of_inj)

/-! ## The enumeration

Generic ∅-axiom `List` membership / nodup helpers live in
`Meta.Tactic.List213` (opened above); this file keeps only the
`Bool`-list-specific enumeration and counting. -/

/-- All length-`n` Bool lists: prepend `false` / `true` to each length-`(n-1)`
    list. -/
def allBoolLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBoolLists n).map (false :: ·) ++ (allBoolLists n).map (true :: ·)

/-- `|allBoolLists n| = 2^n`. -/
theorem allBoolLists_length : ∀ n, (allBoolLists n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
      show ((allBoolLists n).map (false :: ·) ++ (allBoolLists n).map (true :: ·)).length
            = 2 ^ (n + 1)
      rw [length_append, length_map, length_map, allBoolLists_length n,
          Nat.pow_succ, Nat.mul_two]

/-- Every entry of `allBoolLists n` has length `n`. -/
theorem length_of_mem_allBoolLists :
    ∀ {n : Nat} {l : List Bool}, l ∈ allBoolLists n → l.length = n
  | 0, l, h => by
      cases h with
      | head => rfl
      | tail _ h' => nomatch h'
  | n + 1, l, h => by
      rcases mem_append_iff h with h' | h'
      · rcases exists_of_mem_map h' with ⟨t, ht, rfl⟩
        show (false :: t).length = n + 1
        rw [List.length_cons, length_of_mem_allBoolLists ht]
      · rcases exists_of_mem_map h' with ⟨t, ht, rfl⟩
        show (true :: t).length = n + 1
        rw [List.length_cons, length_of_mem_allBoolLists ht]

/-- **Completeness**: every length-`n` Bool list is enumerated. -/
theorem mem_allBoolLists : ∀ (l : List Bool), l ∈ allBoolLists l.length
  | [] => List.Mem.head _
  | b :: l => by
      have ih := mem_allBoolLists l
      show (b :: l) ∈ allBoolLists (l.length + 1)
      show (b :: l) ∈ (allBoolLists l.length).map (false :: ·)
            ++ (allBoolLists l.length).map (true :: ·)
      cases b with
      | false => exact mem_append_left (mem_map_of_mem (false :: ·) ih)
      | true  => exact mem_append_right _ (mem_map_of_mem (true :: ·) ih)

/-! ## No duplicates -/

/-- `map (c :: ·)` preserves `Nodup` (cons with a fixed head is injective);
    `nodup_map_of_inj` specialised to the cons map. -/
private theorem nodup_map_cons {c : Bool} {l : List (List Bool)}
    (h : l.Nodup) : (l.map (c :: ·)).Nodup :=
  nodup_map_of_inj (fun _ _ _ _ hcontra => by injection hcontra) h

/-- **No duplicates**: `allBoolLists n` lists each length-`n` Bool list
    exactly once.  The `false`- and `true`-prefixed blocks are disjoint. -/
theorem nodup_allBoolLists : ∀ n, (allBoolLists n).Nodup
  | 0 => List.Pairwise.cons (by intro y hy; nomatch hy) List.Pairwise.nil
  | n + 1 => by
      show ((allBoolLists n).map (false :: ·) ++ (allBoolLists n).map (true :: ·)).Nodup
      refine nodup_append (nodup_map_cons (nodup_allBoolLists n))
              (nodup_map_cons (nodup_allBoolLists n)) ?_
      intro a hf ht
      rcases exists_of_mem_map hf with ⟨tf, _, rfl⟩
      rcases exists_of_mem_map ht with ⟨_, _, he⟩
      nomatch he

/-! ## Counting constant lists — the count-Lens form of `kernel = 2 constants`

A cochain is in the δ⁰-kernel of a connected `K_{NS,NT}^{(c)}` iff it is a
constant colouring (`KernelConstancyUniversal.isKer_iff_const`).  Counting
the constant length-`n` Bool lists in the enumeration therefore gives the
count-Lens reading of `|ker δ⁰| = 2` (`b₀ = 1`) — **universally and
division-free**, where the existing `kerSizeDelta0Direct = 2` is
`decide`-only (its binary decode pulls core `Nat.div`).

Own count function (core `List.countP` lemmas carry `propext`). -/

/-- Count of entries of a `List (List Bool)` satisfying `p`.  Uses the
    `Bool` conditional `bif` (reduces by `rfl` on literals, unlike the
    `Prop`/`Decidable` `if`). -/
def bcount (p : List Bool → Bool) : List (List Bool) → Nat
  | [] => 0
  | a :: rest => (bif p a then 1 else 0) + bcount p rest

/-- `bcount` distributes over append. -/
theorem bcount_append (p : List Bool → Bool) :
    ∀ (L₁ L₂ : List (List Bool)),
      bcount p (L₁ ++ L₂) = bcount p L₁ + bcount p L₂
  | [], L₂ => (Nat.zero_add _).symm
  | a :: rest, L₂ => by
      show (bif p a then 1 else 0) + bcount p (rest ++ L₂)
            = ((bif p a then 1 else 0) + bcount p rest) + bcount p L₂
      rw [bcount_append p rest L₂, Nat.add_assoc]

/-- `bcount` under `map` reindexes the predicate. -/
theorem bcount_map (p : List Bool → Bool) (f : List Bool → List Bool) :
    ∀ (L : List (List Bool)), bcount p (L.map f) = bcount (fun x => p (f x)) L
  | [] => rfl
  | a :: rest => by
      show (bif p (f a) then 1 else 0) + bcount p (rest.map f)
            = (bif p (f a) then 1 else 0) + bcount (fun x => p (f x)) rest
      rw [bcount_map p f rest]

/-- `bcount p L` is the length of `L.filter p`. -/
theorem filter_length_eq_bcount (p : List Bool → Bool) :
    ∀ (L : List (List Bool)), (L.filter p).length = bcount p L
  | [] => rfl
  | a :: rest => by
      cases h : p a with
      | true =>
          rw [List.filter_cons_of_pos h, List.length_cons,
              filter_length_eq_bcount p rest]
          show bcount p rest + 1 = (bif p a then 1 else 0) + bcount p rest
          rw [h]; exact Nat.add_comm _ _
      | false =>
          rw [List.filter_cons_of_neg (by rw [h]; exact Bool.noConfusion),
              filter_length_eq_bcount p rest]
          show bcount p rest = (bif p a then 1 else 0) + bcount p rest
          rw [h]; exact (Nat.zero_add _).symm

/-- `bcount` respects pointwise-equal predicates. -/
theorem bcount_congr {p q : List Bool → Bool} (h : ∀ x, p x = q x) :
    ∀ (L : List (List Bool)), bcount p L = bcount q L
  | [] => rfl
  | a :: rest => by
      show (bif p a then 1 else 0) + bcount p rest
            = (bif q a then 1 else 0) + bcount q rest
      rw [h a, bcount_congr h rest]

/-- The always-false predicate counts nothing. -/
theorem bcount_false : ∀ (L : List (List Bool)), bcount (fun _ => false) L = 0
  | [] => rfl
  | _ :: rest => by
      show (0 : Nat) + bcount (fun _ => false) rest = 0
      rw [bcount_false rest]

/-! ### The value-fixed predicates -/

/-- All entries are `false`. -/
def isAllFalse : List Bool → Bool
  | [] => true
  | a :: l => (a == false) && isAllFalse l

/-- All entries are `true`. -/
def isAllTrue : List Bool → Bool
  | [] => true
  | a :: l => (a == true) && isAllTrue l

/-- Constant colouring: all-`false` or all-`true`. -/
def isConst (l : List Bool) : Bool := isAllFalse l || isAllTrue l

/-- `bcount` over the `(n+1)`-enumeration splits into the `false`-headed
    and `true`-headed predicate counts at level `n`. -/
theorem bcount_allBoolLists_succ (p : List Bool → Bool) (n : Nat) :
    bcount p (allBoolLists (n + 1))
      = bcount (fun x => p (false :: x)) (allBoolLists n)
        + bcount (fun x => p (true :: x)) (allBoolLists n) := by
  show bcount p ((allBoolLists n).map (false :: ·)
        ++ (allBoolLists n).map (true :: ·)) = _
  rw [bcount_append, bcount_map, bcount_map]

/-- Exactly one length-`n` list is all-`false`. -/
theorem bcount_allFalse : ∀ n, bcount isAllFalse (allBoolLists n) = 1
  | 0 => rfl
  | n + 1 => by
      rw [bcount_allBoolLists_succ,
          show (fun x => isAllFalse (false :: x)) = isAllFalse from rfl,
          show (fun x => isAllFalse (true :: x)) = (fun _ => false) from rfl,
          bcount_false, bcount_allFalse n]

/-- Exactly one length-`n` list is all-`true`. -/
theorem bcount_allTrue : ∀ n, bcount isAllTrue (allBoolLists n) = 1
  | 0 => rfl
  | n + 1 => by
      rw [bcount_allBoolLists_succ,
          show (fun x => isAllTrue (false :: x)) = (fun _ => false) from rfl,
          show (fun x => isAllTrue (true :: x)) = isAllTrue from rfl,
          bcount_false, bcount_allTrue n, Nat.zero_add]

/-- **Count-Lens b₀ = 1**: every nonempty length is realised by exactly
    **two** constant colourings (all-`false`, all-`true`) — the
    division-free universal count matching the structural
    `KernelConstancyUniversal` result `ker δ⁰ = 2 constants`. -/
theorem bcount_const (n : Nat) : bcount isConst (allBoolLists (n + 1)) = 2 := by
  rw [bcount_allBoolLists_succ,
      bcount_congr (p := fun x => isConst (false :: x)) (q := isAllFalse)
        (fun x => Bool.or_false (isAllFalse x)),
      bcount_congr (p := fun x => isConst (true :: x)) (q := isAllTrue)
        (fun x => Bool.false_or (isAllTrue x)),
      bcount_allFalse n, bcount_allTrue n]

/-! ### Half-count: the canonical coboundary representatives

`|im δ⁰| = 2^(V−1)`: a coboundary `δ⁰σ` is determined by `σ` up to a
global constant (`KernelConstancyUniversal`), so each coboundary has a
unique representative with first vertex coloured `false`.  Counting those
representatives gives `dim im δ⁰ = V − 1` — the rank that makes
`b₁ = E − V + 1`. -/

/-- The always-true predicate counts everything. -/
theorem bcount_true : ∀ (L : List (List Bool)), bcount (fun _ => true) L = L.length
  | [] => rfl
  | _ :: rest => by
      show (1 : Nat) + bcount (fun _ => true) rest = rest.length + 1
      rw [bcount_true rest, Nat.add_comm]

/-- First entry is `false`. -/
def headFalse : List Bool → Bool
  | false :: _ => true
  | _ => false

/-- **Half the colourings have first vertex `false`**: exactly `2^n` of
    the `2^(n+1)` length-`(n+1)` lists.  These are the canonical
    coboundary representatives, so `dim im δ⁰ = (n+1) − 1 = n`. -/
theorem bcount_headFalse (n : Nat) :
    bcount headFalse (allBoolLists (n + 1)) = 2 ^ n := by
  rw [bcount_allBoolLists_succ,
      show (fun x => headFalse (false :: x)) = (fun _ => true) from rfl,
      show (fun x => headFalse (true :: x)) = (fun _ => false) from rfl,
      bcount_true, bcount_false, allBoolLists_length n, Nat.add_zero]

/-! ### The complement involution — fibers are `{σ, complement σ}` pairs

A coboundary `δ⁰σ` determines `σ` up to a global constant
(`KernelConstancyUniversal.isKer_iff_const`), so on `V ≥ 1` vertices each
fiber of `δ⁰` is exactly the pair `{σ, complement σ}` (`σ ⊕ all-true`).
The complement map is a fixed-point-free involution, and the head-`false`
colourings pick exactly one element from each pair — so the head-`false`
count `2^(V−1)` is the number of fibers, i.e. `|im δ⁰|`.  These lemmas
establish the transversal structure (the fiber↔pair identification itself
is the cited kernel result). -/

/-- Bitwise complement of a colouring. -/
def complement (l : List Bool) : List Bool := l.map (· == false)

/-- The complement is an involution. -/
theorem complement_involutive : ∀ l, complement (complement l) = l
  | [] => rfl
  | a :: l => by
      show ((a == false) == false) :: complement (complement l) = a :: l
      rw [complement_involutive l]
      cases a <;> rfl

/-- On a nonempty colouring, the complement is not the colouring itself
    (it flips the first entry) — the involution is fixed-point-free. -/
theorem complement_ne_self (a : Bool) (l : List Bool) :
    complement (a :: l) ≠ a :: l := by
  intro h
  -- heads: (a == false) = a, impossible
  have : (a == false) = a := by injection h
  cases a <;> exact Bool.noConfusion this

/-- **Head-`false` is a transversal**: of `σ` and `complement σ` exactly
    one is head-`false` (for a nonempty colouring).  So each
    `{σ, complement σ}` pair has a unique head-`false` representative. -/
theorem headFalse_transversal (a : Bool) (l : List Bool) :
    headFalse (a :: l) = !headFalse (complement (a :: l)) := by
  show headFalse (a :: l) = !headFalse ((a == false) :: complement l)
  cases a <;> rfl

end E213.Lib.Math.Combinatorics.BoolEnum
