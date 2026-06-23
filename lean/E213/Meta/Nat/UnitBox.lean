import E213.Meta.Nat.UnitGrid

/-!
# UnitBox — the rung-3 birthplace of `×`-associativity: the unit box

`UnitList` generated `+`-commutativity (`add_comm_from_append`) and
`+`-associativity (`add_assoc_from_append`) — the additive monoid as the
count-shadow of unit-list append laws. `UnitGrid` generated `×`-commutativity
(`mul_comm_from_grid`) as the grid-transpose double-count.

This file is the level-3 sibling: it generates `×`-**associativity** the same
way, completing the multiplicative monoid `(ℕ, ·, 1)` as a *generated*
discipline. An `a × b × c` box of indistinguishable units — `a` copies of a
`b × c` grid — has a total cell count. Flattening the `a` copies into one
`(a·b) × c` grid and counting by rows reads off `(a·b)·c`. Counting the box
"`a` boxes, each of `b·c` cells" reads off `a·(b·c)`. The two count the *same*
units, so they agree, and `(a·b)·c = a·(b·c)` falls out **without** ever
assuming `Nat.mul_assoc`.

Plumbing note (the generation test): the derivation uses `Nat.add_assoc` /
`Nat.add_comm` (a *different* law — already itself generated in `UnitList`) and
`Nat.succ_mul` / `Nat.zero_mul` (more primitive than `mul_assoc`, upstream of
it in core). It does **not** invoke `Nat.mul_assoc` — the associativity content
comes from the box geometry (`rows_flatten` + `total_join_replicate`), not the
law it generates. All ∅-axiom.
-/

namespace E213.Meta.Nat.UnitBox

open E213.Meta.Nat.UnitList (count fromNat)
open E213.Meta.Nat.UnitGrid (UGrid total replicate rows total_rows)

/-- `replicate (m + n) x = replicate m x ++ replicate n x`. -/
theorem replicate_add {α : Type} (x : α) :
    ∀ (m n : Nat), replicate (m + n) x = replicate m x ++ replicate n x
  | 0,     n => by rw [Nat.zero_add]; rfl
  | m + 1, n => by
      rw [Nat.succ_add]
      show x :: replicate (m + n) x = x :: (replicate m x ++ replicate n x)
      rw [replicate_add x m n]

/-- `total` is additive over grid concatenation (uses `Nat.add_assoc` — a law
    distinct from the `mul_assoc` being generated). -/
theorem total_append : ∀ (g h : UGrid), total (g ++ h) = total g + total h
  | [],     h => (Nat.zero_add (total h)).symm
  | r :: g, h => by
      show count r + total (g ++ h) = (count r + total g) + total h
      rw [total_append g h, Nat.add_assoc]

/-- Total of a `join` of `a` identical grids `g` is `a · total g`.
    (`a` copies, counted; the multiplicative content has not yet appeared.) -/
theorem total_join_replicate (g : UGrid) :
    ∀ (a : Nat), total ((replicate a g).join) = a * total g
  | 0     => by show total ([] : UGrid) = 0 * total g; rw [Nat.zero_mul]; rfl
  | a + 1 => by
      show total (g ++ (replicate a g).join) = (a + 1) * total g
      rw [total_append g ((replicate a g).join), total_join_replicate g a,
          Nat.succ_mul, Nat.add_comm]

/-- **The box flattens to a grid**: `a` copies of the `b × c` grid, joined, is
    the `(a·b) × c` grid. (Uses `replicate_add` + `Nat.succ_mul`/`add_comm`;
    no `mul_assoc`.) -/
theorem rows_flatten (b c : Nat) :
    ∀ (a : Nat), (replicate a (rows b c)).join = rows (a * b) c
  | 0     => by show ([] : UGrid) = rows (0 * b) c; rw [Nat.zero_mul]; rfl
  | a + 1 => by
      show rows b c ++ (replicate a (rows b c)).join = rows ((a + 1) * b) c
      rw [rows_flatten b c a]
      show replicate b (fromNat c) ++ replicate (a * b) (fromNat c)
            = replicate ((a + 1) * b) (fromNat c)
      rw [Nat.succ_mul, Nat.add_comm (a * b) b, replicate_add (fromNat c) b (a * b)]

/-- ★★★★★ **Associativity of `·` is the shadow of the unit box double-count**:
    counting an `a × b × c` box as one `(a·b) × c` grid gives `(a·b)·c`;
    counting it as `a` boxes of `b·c` cells gives `a·(b·c)`; the box is the
    same units, so the two counts agree. Generated, not presupposed — the cone
    does not invoke `Nat.mul_assoc`. Completes the multiplicative monoid as a
    generated discipline alongside `UnitGrid.mul_comm_from_grid`. -/
theorem mul_assoc_from_box (a b c : Nat) : (a * b) * c = a * (b * c) :=
  calc (a * b) * c
      = total (rows (a * b) c)              := (total_rows (a * b) c).symm
    _ = total ((replicate a (rows b c)).join) := by rw [rows_flatten b c a]
    _ = a * total (rows b c)               := total_join_replicate (rows b c) a
    _ = a * (b * c)                        := by rw [total_rows b c]

end E213.Meta.Nat.UnitBox
