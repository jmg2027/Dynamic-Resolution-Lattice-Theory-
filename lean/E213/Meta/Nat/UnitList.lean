import E213.Meta.Nat.PureNat

/-!
# UnitList — the rung below `+`: append, and where commutativity is born

The slot programme's floor, one diagonal below `+`
(`research-notes/frontiers/numbersystem_square.md`,
`book/slots/01`): the sorted list is the list of **units** — elements
with no distinguishing marks, so "insertion order" and "sorted order"
coincide and no sorting is ever needed: the order *is* the element
count.

Derived here from list induction alone, no algebra remembered:

* `append` is associative for any element type (free), and **not**
  commutative in general (`append_not_comm_general`: `[a]++[b] ≠
  [b]++[a]` for distinguishable elements);
* on unit lists commutativity is **born**
  (`append_comm`): indistinguishable elements bubble freely;
* `+` is the count-readout of append (`count_append`), and the
  commutativity of `+` is then the **shadow** of unit-list append
  commutativity (`add_comm_from_append`) — counting forgets
  arrangement, and what survives the forgetting is commutative.

Two readings, both Lens choices on the same object: the completed
list with operations as *addresses* into it, or the operations as
*applications of append* — the readout view and the fold view.

All ∅-axiom; self-contained inductions (no core `List` lemmas).
-/

namespace E213.Meta.Nat.UnitList

/-- The sorted list: a list of indistinguishable units.  "Sorted" is
    free — there is nothing to sort. -/
abbrev UList := List Unit

/-- Appending nothing on the right. -/
theorem append_nil : ∀ (l : List Unit), l ++ [] = l
  | [] => rfl
  | _ :: l => congrArg _ (append_nil l)

/-- A unit bubbles to the front of any append: all elements are the
    unit, so positions carry no information. -/
theorem append_cons : ∀ (l m : List Unit) (u : Unit),
    l ++ (u :: m) = u :: (l ++ m)
  | [], _, _ => rfl
  | _ :: l, m, u => congrArg _ (append_cons l m u)

/-- ★★★★ **Commutativity is born here**: unit-list append commutes —
    derived by bare induction, not assumed.  (General append does
    not: `append_not_comm_general`.) -/
theorem append_comm : ∀ (l m : List Unit), l ++ m = m ++ l
  | [], m => (append_nil m).symm
  | u :: l, m => by
    show u :: (l ++ m) = m ++ (u :: l)
    rw [append_cons m l u, append_comm l m]

/-- General append is **not** commutative: distinguishable elements
    remember their arrangement. -/
theorem append_not_comm_general :
    ([true] ++ [false]) ≠ ([false] ++ [true]) := by
  intro h
  exact Bool.noConfusion (List.cons.inj h).1

/-- The count readout: how many units. -/
def count : List Unit → Nat
  | [] => 0
  | _ :: l => count l + 1

/-- ★★★★ `+` is the count-readout of append. -/
theorem count_append : ∀ (l m : List Unit),
    count (l ++ m) = count m + count l
  | [], m => rfl
  | _ :: l, m => by
    show count (l ++ m) + 1 = count m + (count l + 1)
    rw [count_append l m, Nat.add_assoc]

/-- The number `n` as a unit list. -/
def fromNat : Nat → List Unit
  | 0 => []
  | n + 1 => () :: fromNat n

theorem count_fromNat : ∀ n : Nat, count (fromNat n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (count_fromNat n)

/-- ★★★★★ **The commutativity of `+` is the shadow of unit-list
    append commutativity**: counting forgets arrangement, and what
    survives the forgetting commutes.  Not a replacement for
    `Nat.add_comm` — its derivation, one rung down. -/
theorem add_comm_from_append (a b : Nat) : a + b = b + a :=
  calc a + b
      = count (fromNat b ++ fromNat a) := by
        rw [count_append, count_fromNat, count_fromNat]
    _ = count (fromNat a ++ fromNat b) := by rw [append_comm]
    _ = b + a := by
        rw [count_append, count_fromNat, count_fromNat]

end E213.Meta.Nat.UnitList
