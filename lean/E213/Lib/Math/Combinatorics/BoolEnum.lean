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

open E213.Tactic.List213 (length_append length_map)

/-! ## Pure `List` membership / nodup helpers

Core `List.mem_map`, `List.mem_append`, `List.Nodup` lemmas carry
`propext`; these hand-proofs stay ∅-axiom. -/

/-- `b ∈ l → f b ∈ l.map f`. -/
theorem mem_map_of_mem {α β : Type _} (f : α → β) {b : α} :
    ∀ {l : List α}, b ∈ l → f b ∈ l.map f
  | _ :: _, List.Mem.head _ => List.Mem.head _
  | _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_map_of_mem f h)

/-- `a ∈ l.map f → ∃ b ∈ l, f b = a`. -/
theorem exists_of_mem_map {α β : Type _} {f : α → β} {a : β} :
    ∀ {l : List α}, a ∈ l.map f → ∃ b, b ∈ l ∧ f b = a
  | x :: _, List.Mem.head _ => ⟨x, List.Mem.head _, rfl⟩
  | _ :: xs, List.Mem.tail _ h =>
      let ⟨b, hb, hfb⟩ := exists_of_mem_map (l := xs) h
      ⟨b, List.Mem.tail _ hb, hfb⟩

/-- `a ∈ l₁ → a ∈ l₁ ++ l₂`. -/
theorem mem_append_left {α : Type _} {a : α} {l₂ : List α} :
    ∀ {l₁ : List α}, a ∈ l₁ → a ∈ l₁ ++ l₂
  | _ :: _, List.Mem.head _ => List.Mem.head _
  | _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_append_left h)

/-- `a ∈ l₂ → a ∈ l₁ ++ l₂`. -/
theorem mem_append_right {α : Type _} {a : α} :
    ∀ (l₁ : List α) {l₂ : List α}, a ∈ l₂ → a ∈ l₁ ++ l₂
  | [], _, h => h
  | _ :: xs, _, h => List.Mem.tail _ (mem_append_right xs h)

/-- Membership in an append splits. -/
theorem mem_append_iff {α : Type _} {a : α} {l₁ l₂ : List α}
    (h : a ∈ l₁ ++ l₂) : a ∈ l₁ ∨ a ∈ l₂ := by
  induction l₁ with
  | nil => exact Or.inr h
  | cons x xs ih =>
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h' => exact (ih h').imp (List.Mem.tail _) id

/-! ## The enumeration -/

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

/-- Append preserves `Nodup` when the two lists are disjoint.  Pure
    induction on the first list (core `List.nodup_append` is an `iff`,
    carrying `propext`). -/
theorem nodup_append {α : Type _} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ a, a ∈ l₁ → a ∈ l₂ → False) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => exact h₂
  | cons x xs ih =>
      cases h₁ with
      | cons hx hxs =>
          refine List.Pairwise.cons ?_
            (ih hxs (fun a ha hb => hd a (List.Mem.tail _ ha) hb))
          intro y hy
          rcases mem_append_iff hy with hy₁ | hy₂
          · exact hx y hy₁
          · exact fun he => hd x (List.Mem.head _) (he ▸ hy₂)

/-- `map (c :: ·)` preserves `Nodup` (cons with a fixed head is injective). -/
theorem nodup_map_cons {c : Bool} :
    ∀ {l : List (List Bool)}, l.Nodup → (l.map (c :: ·)).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
      cases h with
      | cons hx hxs =>
          refine List.Pairwise.cons ?_ (nodup_map_cons hxs)
          intro y hy
          rcases exists_of_mem_map hy with ⟨t', ht', rfl⟩
          intro hcontra
          have hxt : x = t' := by injection hcontra
          exact hx t' ht' hxt

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

end E213.Lib.Math.Combinatorics.BoolEnum
