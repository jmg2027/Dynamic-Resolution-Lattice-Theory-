import E213.Meta.Tactic.List213

/-!
# BinTree213 — the tree floor below append

One rung below `UnitList` (`E213/Meta/Nat/UnitList.lean`, the *append*
floor where `+`-comm is born): the free **binary magma**.  Gluing two
trees remembers how they were bracketed — `node` is a raw, unquotiented
binary operation, associativity **deliberately absent**.

The free binary tree carries TWO quotient maps:

* mod **associativity** → `List` / append (*this file*): `flatten`
  keeps left-to-right order but forgets bracketing
  (`flatten_assoc_collapse`).  The freely-given `append_assoc` of
  `UnitList`/`List213` is *precisely* the bracketing-collapse this
  file proves — `append`'s associativity is the identification
  `flatten` performs.
* mod **commutativity** → `Raw.slash` (`Theory/Raw/ParenthesizationDistinct`,
  the conceptual sibling — *not* imported; `Meta/Nat` stays
  ring-independent): keeps bracketing, forgets order.

Quotient by BOTH → the commutative monoid; and `count` on units
(`UnitList`) forgets everything but length.  So at the bottom of the
tower bracketing is real (`node_not_assoc`); flatten erases it into
order (the `List`); count erases order into a number (`Nat`).  At the
*top* of the tower the same non-associativity returns as the `^`-wall
(`^` is non-associative — `numbersystem_square` frontier, `HyperAssoc`).

Order of forgetting:
  `BinTree` ──flatten──▶ `List` ──length──▶ `Nat`
  (remembers bracketing) (remembers order) (remembers only count)

All ∅-axiom; bare inductions / `congrArg` / `noConfusion`, and the PURE
`List213.append_assoc` (core `List.append_assoc` carries `propext`).
-/

namespace E213.Meta.Nat.BinTree213

open E213.Tactic.List213 (append_assoc length_append)

/-- The free binary magma: a non-associative tree that remembers its
    bracketing.  `node` glues two trees; `leaf` is an atom. -/
inductive BinTree (α : Type _) where
  | leaf : α → BinTree α
  | node : BinTree α → BinTree α → BinTree α

open BinTree (leaf node)

/-- The associativity-quotient map: forget bracketing, keep order.
    `flatten (leaf a) = [a]`, `flatten (node l r) = flatten l ++ flatten r`. -/
def flatten {α : Type _} : BinTree α → List α
  | .leaf a   => [a]
  | .node l r => flatten l ++ flatten r

/-- ★ **Bracketing is REAL in the magma.**  The two re-bracketings of
    three leaves are distinct trees: one has a `node` left child, the
    other a `leaf` left child — `noConfusion` separates them (no
    decidability, no `propext`).  This is the non-associativity of the
    floor-below-the-floor. -/
theorem node_not_assoc {α : Type _} (a b c : α) :
    node (node (leaf a) (leaf b)) (leaf c)
      ≠ node (leaf a) (node (leaf b) (leaf c)) := by
  intro h
  have hl : node (leaf a) (leaf b) = leaf a := (BinTree.node.inj h).1
  exact BinTree.noConfusion hl

/-- ★★ **append is the associativity-quotient of the binary tree.**
    The two distinct bracketings (`node_not_assoc`) flatten to the SAME
    list, because both equal `flatten l ++ flatten m ++ flatten r` — and
    that identity is *exactly* the PURE `List213.append_assoc`.  So
    `append_assoc` IS the bracketing-collapse `flatten` performs. -/
theorem flatten_assoc_collapse {α : Type _} (l m r : BinTree α) :
    flatten (node (node l m) r) = flatten (node l (node m r)) := by
  show (flatten l ++ flatten m) ++ flatten r
      = flatten l ++ (flatten m ++ flatten r)
  exact append_assoc (flatten l) (flatten m) (flatten r)

/-- The leaf-count readout: how many atoms, by bare recursion.  One
    further forgetting than `flatten` (drops order too). -/
def count {α : Type _} : BinTree α → Nat
  | .leaf _   => 1
  | .node l r => count l + count r

/-- The leaf-count is the length of the flattening: `count` factors
    through `flatten`, then the PURE `List213.length_append`. -/
theorem count_eq_length_flatten {α : Type _} :
    ∀ t : BinTree α, count t = (flatten t).length
  | .leaf _   => rfl
  | .node l r => by
      show count l + count r = (flatten l ++ flatten r).length
      rw [length_append, count_eq_length_flatten l, count_eq_length_flatten r]

/-- ★ The `ℕ` readout is blind to bracketing — one further forgetting
    than `flatten` (which still distinguishes order).  The bare form
    keeps the dependency floor (`Nat.add_assoc`). -/
theorem count_assoc_blind {α : Type _} (l m r : BinTree α) :
    count (node (node l m) r) = count (node l (node m r)) := by
  show (count l + count m) + count r = count l + (count m + count r)
  rw [Nat.add_assoc]

end E213.Meta.Nat.BinTree213
