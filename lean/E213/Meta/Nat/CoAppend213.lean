import E213.Meta.Tactic.List213
import E213.Meta.Nat.ListLocate213

/-!
# CoAppend213 — the co-operation dual of append: splitting

Everything in the slot programme glues two into one: `append`, `+`, `×`
are `(a, b) ↦ c`.  The **dual** splits one into two — the
**comultiplication** `c ↦ (a, b)` — and for the list floor that is
`splits`: all `(prefix, suffix)` cuts of a list.

The unification this file pins (`mem_splits_iff`): **a split *is* an
append-witness.**  `(l1, l2) ∈ splits l ↔ l1 ++ l2 = l` — membership in
the comultiplication is *exactly* the witness relation `l1 ++ l2 = l`,
i.e. the `+`-inverse question "what glues with `l2` to give `l`".  So the
**inverse questions** that grow ℤ / ℚ (`a + x = b`, `a · x = b` solved for
`x`) are **co-operations (splittings), not inverse operations** — which is
precisely why the slot programme's witness-form discipline
(`theory/math/numbersystems/slot_arithmetic.md`: "`a = c + e`, never
`a − c`") never imports an inverse operation: it is working with the
co-operation directly.  Number-system growth = forcing the co-operation
**total** (group completion = splitting-closure); convolution =
split-then-reglue, a new operation off the `+×^` diagonal (next brick).

Readouts dualize too: the operation's size is one number (`count`); the
**co-operation's size is `length + 1`** (`length_splits`) — a length-`n`
list has `n + 1` cuts.  And the split is **functional in either part**
(`split_functional`): fixing `l1`, the suffix `l2` is determined — the
co-operation is single-valued, the way subtraction's result is.

All ∅-axiom; bare recursion / `List.Mem` with the PURE `List213`
membership helpers (core `List.mem_*`/`map`/`length` carry `propext`).
-/

namespace E213.Meta.Nat.CoAppend213

universe u

open E213.Tactic.List213 (length_map mem_map_of_mem exists_of_mem_map)
open E213.Meta.Nat.ListLocate213 (append_cancel)

/-- The **co-operation dual of append**: every `(prefix, suffix)` cut of a
    list.  `splits [] = [([],[])]`; `splits (x :: l)` is the empty-left cut
    `([], x :: l)` plus `x` prepended to every cut of `l`. -/
def splits {α : Type u} : List α → List (List α × List α)
  | []     => [([], [])]
  | x :: l => ([], x :: l) :: (splits l).map (fun p => (x :: p.1, p.2))

/-- The empty-left cut is always present (the head of `splits l`). -/
theorem nil_split_mem {α : Type u} (l : List α) : ([], l) ∈ splits l := by
  cases l with
  | nil      => exact List.Mem.head _
  | cons _ _ => exact List.Mem.head _

/-- Forward direction of the unification: every split reglues. -/
theorem mem_splits_imp {α : Type u} :
    ∀ (l l1 l2 : List α), (l1, l2) ∈ splits l → l1 ++ l2 = l
  | [],     _, _, h => by
      cases h with
      | head      => rfl
      | tail _ h' => nomatch h'
  | x :: l, _, _, h => by
      cases h with
      | head => rfl
      | tail _ h' =>
          obtain ⟨p, hp, hpe⟩ := exists_of_mem_map h'
          injection hpe with e1 e2
          subst e1; subst e2
          show x :: (p.1 ++ p.2) = x :: l
          have hp' : (p.1, p.2) ∈ splits l := hp
          rw [mem_splits_imp l p.1 p.2 hp']

/-- Backward direction: every append-witness is a split. -/
theorem mem_splits_of_eq {α : Type u} :
    ∀ (l1 l2 l : List α), l1 ++ l2 = l → (l1, l2) ∈ splits l
  | [],      l2, l, h => by
      subst h
      exact nil_split_mem _
  | a :: l1, l2, l, h => by
      subst h
      exact List.Mem.tail _
        (mem_map_of_mem (fun p => (a :: p.1, p.2))
          (mem_splits_of_eq l1 l2 (l1 ++ l2) rfl))

/-- ★★ **A split IS an append-witness.**  `(l1, l2) ∈ splits l ↔
    l1 ++ l2 = l`: the comultiplication's membership relation is exactly
    the `+`-inverse question.  The inverse questions that mint ℤ / ℚ are
    co-operations, not inverse operations. -/
theorem mem_splits_iff {α : Type u} (l1 l2 l : List α) :
    (l1, l2) ∈ splits l ↔ l1 ++ l2 = l :=
  ⟨mem_splits_imp l l1 l2, mem_splits_of_eq l1 l2 l⟩

/-- ★ Every split reglues to the whole — `splits` is a section of append
    (the co-operation inverts the operation). -/
theorem splits_glue {α : Type u} (l1 l2 l : List α)
    (h : (l1, l2) ∈ splits l) : l1 ++ l2 = l :=
  mem_splits_imp l l1 l2 h

/-- ★ **The co-operation's size is `length + 1`.**  A length-`n` list has
    `n + 1` cuts — dual to `count` (the operation's size is one number). -/
theorem length_splits {α : Type u} :
    ∀ (l : List α), (splits l).length = l.length + 1
  | []     => rfl
  | x :: l => by
      show ((splits l).map (fun p => (x :: p.1, p.2))).length + 1
          = (l.length + 1) + 1
      rw [length_map, length_splits l]

/-- ★ **The split is functional in the prefix**: fixing `l1`, the suffix is
    determined (`l1 ++ l2 = l ∧ l1 ++ l2' = l → l2 = l2'`).  The
    co-operation is single-valued — the way subtraction's result is. -/
theorem split_functional {α : Type u} (l1 l2 l2' l : List α)
    (h : l1 ++ l2 = l) (h' : l1 ++ l2' = l) : l2 = l2' :=
  append_cancel l1 l2 l2' (h.trans h'.symm)

end E213.Meta.Nat.CoAppend213
