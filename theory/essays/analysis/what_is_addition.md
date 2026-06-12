# What is `+`?

`+` is the count-Lens's binary shadow: the operation `(ℕ, ℕ) → ℕ` that
the readout `count : List → ℕ` transports `append` to.  For any lists of
counts `a` and `b`, `a + b = count (lₐ ++ l_b)`.  It is not an axiom —
it is what counting does to gluing.

## 213-native answer

`+` is the operation `ℕ` inherits from `append` under the count-Lens.
`count` is a monoid homomorphism `(List, ++) → (ℕ, +)`:
`count (l ++ m) = count m + count l` (`UnitList.count_append`).  So `+`
has no content of its own — it is `append` seen through the readout that
forgets arrangement and keeps only length.

## Derivation

Unfold `count` itself and `+` reduces further.  Counting is repeated
`+1`: `count [] = 0`, `count (() :: l) = count l + 1`.  The binary `+`
is then *iterated `+1`* — `a + b = iter Nat.succ b a` (apply "one more
unit" `b` times to `a`, `Iterate213.add_eq_iter`).  And `+1` is the
successor `() ::`, "one more unit"; the unit is a single distinguishing
act — the naming event of `seed/AXIOM/06_lens_readings.md` §6.5, the
count-Lens activating once more.  So **`+` is iterated distinguishing,
counted**.  Below `+` there is only the act of distinguishing; nothing
is more primitive, because distinguishing is what the residue does when
it points at itself (§6.5; ℕ is the count-Lens image, §6.7).

`+` *is* order.  Its witness question founds comparison: `a ≤ b ↔ ∃x,
a + x = b`, and the strict positive-witness `a < b ↔ ∃x, a + (x+1) = b`
founds *location* — the unique slot strictly between `a` and its
next-next (`StrictLocate213.locate_strict`,
`theory/math/numbersystems/slot_arithmetic.md` §2).  To ask "where is
`b` relative to `a`" is to solve a `+`.  Order and `+` are one operation.

`+` is self-dual at the floor.  Forward, it glues two counts; backward,
it is the total a split reglues to — `(l1, l2) ∈ splits l ↔ l1 ++ l2 =
l` (`CoAppend213.mem_splits_iff`), and `count l1 + count l2 = count l`.
The same `+` is "combine two" and "the whole of a cut".

`+` is the nicest rung because it iterates the *most* primitive action:
adding a structureless unit.  The unit's indistinguishability is exactly
what makes `+` commutative and associative for free — `append_comm` on
units becomes `add_comm_from_append` (`UnitList`), and `append`'s
associativity is the bracketing the unit list never had
(`BinTree213.flatten_assoc_collapse`).  Commutativity and associativity
of `+` are not assumed; they fall out of the unit having no structure.

## Dual function

This is classical "addition" with its packaging stripped.  Peano's
successor axioms *are* "`+` = iterated successor"; 213 only renames the
successor as the count-Lens's unit-distinguishing event, so `+` is a
*readout* of the residue's pointings, not a primitive of an axiom
system — and its commutativity and associativity, postulated or proved
by induction classically, are here forced by the unit's
structurelessness, sharper because nothing is assumed.

## Cross-frame connections

Four readings, one operation: count of append (`count_append`),
iterated successor (`add_eq_iter`), the order-founding witness
(`a + x = b`, `locate_strict`), and the reglue of a split
(`mem_splits_iff`).  They converge — counting *is* iterating `+1` *is*
measuring how far apart *is* the total of the parts.  Same fact, four
resolutions; the convergence is why `+` looks elementary yet anchors the
whole tower (`Iterate213`: every rung is `iter` at a heavier action).

## Open frontier

None at this rung — `+` is the most closed operation in the tower.  The
floor it rests on ("below `+1` there is only distinguishing") is not an
open problem but the no-exterior bottom: the residue pointing at itself
(§6.5), with no simpler-than-itself version beneath.
