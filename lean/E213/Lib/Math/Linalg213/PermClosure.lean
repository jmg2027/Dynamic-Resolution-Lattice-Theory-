import E213.Lib.Math.Linalg213.Permutation

/-!
# Linalg213 — the permutation enumeration realizes the symmetric-group action

The remaining gate for the Leibniz determinant's **alternating** property: the enumeration
`perms n` is closed (up to `LPerm`) under an adjacent position-swap `swapAt k`, and every
listed permutation is a genuine rearrangement of `[0,…,n−1]` (sound) with no repeats (nodup).

This file builds that closure bottom-up: clean (∅-axiom) `List` membership helpers → `LPerm`
structural lemmas → enumeration **soundness** (each output is a rearrangement) → (later)
completeness, nodup, and the closure itself.

The core `List.mem_*` iff-lemmas are `propext`/`Quot.sound`-tainted, so membership is done
structurally on the `List.Mem` constructors.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.PermClosure

open E213.Lib.Math.Linalg213.Permutation
  (LPerm insertEverywhere permsOf perms swapAt swapAt_lperm)

/-! ## §0 — clean (∅-axiom) `List` membership helpers -/

/-- `q ∈ L1 ++ L2 → q ∈ L1 ∨ q ∈ L2` (structural, no `propext`). -/
theorem mem_append' {α : Type} {q : α} : ∀ {L1 L2 : List α}, q ∈ L1 ++ L2 → q ∈ L1 ∨ q ∈ L2
  | [],      _,  h => Or.inr h
  | _ :: _,  _,  h => by
    cases h with
    | head      => exact Or.inl (List.Mem.head _)
    | tail _ h' => rcases mem_append' h' with h1 | h2
                   · exact Or.inl (List.Mem.tail _ h1)
                   · exact Or.inr h2

/-- `q ∈ L.map f → ∃ x ∈ L, f x = q` (structural). -/
theorem mem_map' {α β : Type} (f : α → β) {q : β} : ∀ {L : List α},
    q ∈ L.map f → ∃ x, x ∈ L ∧ f x = q
  | [],      h => by cases h
  | a :: as, h => by
    cases h with
    | head      => exact ⟨a, List.Mem.head _, rfl⟩
    | tail _ h' => rcases mem_map' f h' with ⟨x, hx, e⟩; exact ⟨x, List.Mem.tail _ hx, e⟩

/-- `q ∈ L.flatMap f → ∃ x ∈ L, q ∈ f x` (structural). -/
theorem mem_flatMap' {α β : Type} (f : α → List β) {q : β} : ∀ {L : List α},
    q ∈ L.flatMap f → ∃ x, x ∈ L ∧ q ∈ f x
  | [],      h => by cases h
  | a :: as, h => by
    rcases mem_append' h with h1 | h2
    · exact ⟨a, List.Mem.head _, h1⟩
    · rcases mem_flatMap' f h2 with ⟨x, hx, hqx⟩; exact ⟨x, List.Mem.tail _ hx, hqx⟩

/-- `q ∈ [a] → q = a` (structural). -/
theorem mem_singleton' {α : Type} {q a : α} (h : q ∈ [a]) : q = a := by
  cases h with
  | head      => rfl
  | tail _ h' => cases h'

/-! ## §1 — `LPerm` structural lemmas -/

/-- `LPerm` preserves membership. -/
theorem LPerm.mem {α : Type} {a : α} {L1 L2 : List α} (h : LPerm L1 L2) : a ∈ L1 → a ∈ L2 := by
  induction h with
  | nil => exact id
  | cons x _ ih =>
    intro hm
    cases hm with
    | head      => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (ih h')
  | swap x y l =>
    intro hm
    cases hm with
    | head      => exact List.Mem.tail _ (List.Mem.head _)
    | tail _ h' =>
      cases h' with
      | head       => exact List.Mem.head _
      | tail _ h'' => exact List.Mem.tail _ (List.Mem.tail _ h'')
  | trans _ _ ih₁ ih₂ => intro hm; exact ih₂ (ih₁ hm)

/-- An adjacent swap after a prefix is an `LPerm`. -/
theorem lperm_swap_prefix {α : Type} (pre : List α) (x y : α) (l : List α) :
    LPerm (pre ++ x :: y :: l) (pre ++ y :: x :: l) := by
  induction pre with
  | nil          => exact LPerm.swap y x l
  | cons a pre ih => exact LPerm.cons a ih

/-! ## §2 — enumeration soundness (every output is a rearrangement) -/

/-- Every list produced by `insertEverywhere a p` is a rearrangement of `a :: p`. -/
theorem insEv_sound (a : Nat) : ∀ (p q : List Nat), q ∈ insertEverywhere a p → LPerm q (a :: p)
  | [],      q, h => by
    have hq : q = [a] := mem_singleton' h
    subst hq; exact LPerm.refl [a]
  | b :: ys, q, h => by
    cases h with
    | head => exact LPerm.refl (a :: b :: ys)
    | tail _ hmap =>
      rcases mem_map' _ hmap with ⟨q', hq', hb⟩
      subst hb
      exact LPerm.trans (LPerm.cons b (insEv_sound a ys q' hq')) (LPerm.swap a b ys)

/-- Every list in `permsOf xs` is a rearrangement of `xs`. -/
theorem permsOf_sound : ∀ (xs q : List Nat), q ∈ permsOf xs → LPerm q xs
  | [],      q, h => by
    have hq : q = [] := mem_singleton' h
    subst hq; exact LPerm.nil
  | a :: ys, q, h => by
    rcases mem_flatMap' _ h with ⟨p, hp, hq⟩
    exact LPerm.trans (insEv_sound a p q hq) (LPerm.cons a (permsOf_sound ys p hp))

end E213.Lib.Math.Linalg213.PermClosure
