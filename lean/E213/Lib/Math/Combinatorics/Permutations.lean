import E213.Meta.Tactic.List213

/-!
# Permutation enumeration with factorial cardinality (∅-axiom)

The shared infrastructure the *named* proof-ISA bounds need
(`research-notes/frontiers/`): an explicit enumeration of all orderings of a
list, with its cardinality `= n!`.  `LPerm` (permutation *equivalence*,
`Algebra/Linalg213/Permutation.lean`) names the relation; this names the
enumeration carrying `length = n!` — the count Sperner's chain side needs
(`#maximal chains of 2^[n] = n!`) and the same factorial the Leibniz
determinant sums over.

  · `insertEverywhere a l` — the `|l|+1` ways to drop `a` into `l`;
  · `perms l` — all orderings of `l`, by inserting each head everywhere;
  · ★ `perms_length : (perms l).length = fact l.length` — the `n!` count.

Mathlib-free: a private `flatMap213` (core `List.flatMap` carries `propext`) and
the `Meta.Tactic.List213` length/membership toolkit.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.Permutations

open E213.Tactic.List213
  (length_append length_map mem_append_iff exists_of_mem_map)

/-! ## §1 — factorial -/

/-- `n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-! ## §2 — concat-map (propext-free `flatMap`) -/

/-- `flatMap` without the core `propext` dependency. -/
def flatMap213 {α β : Type _} (f : α → List β) : List α → List β
  | [] => []
  | a :: l => f a ++ flatMap213 f l

/-- Membership in a `flatMap213` exposes the witness it came from. -/
theorem mem_flatMap213 {α β : Type _} {f : α → List β} {q : β} :
    ∀ {l : List α}, q ∈ flatMap213 f l → ∃ a, a ∈ l ∧ q ∈ f a
  | [], h => nomatch h
  | a :: l, h => by
      rcases mem_append_iff (l₁ := f a) (l₂ := flatMap213 f l) h with h1 | h2
      · exact ⟨a, List.Mem.head _, h1⟩
      · obtain ⟨a', ha', hq'⟩ := mem_flatMap213 h2
        exact ⟨a', List.Mem.tail _ ha', hq'⟩

/-- If every fibre `f x` (for `x ∈ L`) has the same length `c`, the total is
    `c · |L|` — the cardinality of a constant-fibre `flatMap`. -/
theorem length_flatMap213_const {α β : Type _} (f : α → List β) (c : Nat) :
    ∀ {L : List α}, (∀ x, x ∈ L → (f x).length = c) → (flatMap213 f L).length = c * L.length
  | [], _ => (Nat.mul_zero c).symm
  | a :: l, h => by
      show (f a ++ flatMap213 f l).length = c * (l.length + 1)
      rw [length_append, h a (List.Mem.head _),
          length_flatMap213_const f c (fun x hx => h x (List.Mem.tail _ hx)),
          Nat.mul_add, Nat.mul_one]
      exact Nat.add_comm c (c * l.length)

/-! ## §3 — insertion and the enumeration -/

/-- All `|l| + 1` ways to insert `a` into `l`. -/
def insertEverywhere {α : Type _} (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertEverywhere a l).map (b :: ·)

/-- Inserting `a` produces exactly `|l| + 1` lists. -/
theorem insertEverywhere_length {α : Type _} (a : α) :
    ∀ l : List α, (insertEverywhere a l).length = l.length + 1
  | [] => rfl
  | b :: l => by
      show ((a :: b :: l) :: (insertEverywhere a l).map (b :: ·)).length = (b :: l).length + 1
      rw [List.length_cons, length_map, insertEverywhere_length a l, List.length_cons]

/-- Every insertion lengthens its input by one. -/
theorem mem_insertEverywhere_length {α : Type _} (a : α) :
    ∀ (l q : List α), q ∈ insertEverywhere a l → q.length = l.length + 1
  | [], q, h => by
      cases h with
      | head => rfl
      | tail _ h' => nomatch h'
  | b :: l, q, h => by
      cases h with
      | head => rfl
      | tail _ h' =>
          obtain ⟨q', hq', rfl⟩ := exists_of_mem_map h'
          have hlen := mem_insertEverywhere_length a l q' hq'
          show (b :: q').length = (b :: l).length + 1
          rw [List.length_cons, List.length_cons, hlen]

/-- All orderings of `l`: insert each head into every ordering of the tail. -/
def perms {α : Type _} : List α → List (List α)
  | [] => [[]]
  | a :: l => flatMap213 (insertEverywhere a) (perms l)

/-- Every ordering has the original length. -/
theorem perms_length_const {α : Type _} :
    ∀ (l p : List α), p ∈ perms l → p.length = l.length
  | [], p, h => by
      cases h with
      | head => rfl
      | tail _ h' => nomatch h'
  | a :: l, p, h => by
      obtain ⟨q, hq, hpq⟩ := mem_flatMap213 h
      have hql : q.length = l.length := perms_length_const l q hq
      have hpl : p.length = q.length + 1 := mem_insertEverywhere_length a q p hpq
      rw [hpl, hql]
      exact (List.length_cons a l).symm

/-- ★ **The `n!` count.**  `perms` enumerates exactly `|l|!` orderings.  Each
    head inserted everywhere multiplies the tail's `(|l|)!` orderings by the
    `|l|+1` insertion slots — the factorial recursion, on the nose. -/
theorem perms_length {α : Type _} : ∀ (l : List α), (perms l).length = fact l.length
  | [] => rfl
  | a :: l => by
      show (flatMap213 (insertEverywhere a) (perms l)).length = fact (l.length + 1)
      have hc : ∀ p, p ∈ perms l → (insertEverywhere a p).length = l.length + 1 := by
        intro p hp
        rw [insertEverywhere_length a p, perms_length_const l p hp]
      rw [length_flatMap213_const (insertEverywhere a) (l.length + 1) hc, perms_length l]
      show (l.length + 1) * fact l.length = fact (l.length + 1)
      rfl

end E213.Lib.Math.Combinatorics.Permutations
