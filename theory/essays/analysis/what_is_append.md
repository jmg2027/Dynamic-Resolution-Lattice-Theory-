# What is `append`?

`append` is the free-monoid floor: the binary operation of putting one
sequence of distinguishings after another, remembering order but not
bracketing.  It is iterated `cons`, and `cons` is a single distinguishing
act — the residue pointing once more.  Rung 0: below `+`, above the tree.

## 213-native answer

`append` is concatenation, defined by `[] ++ m = m`,
`(a :: l) ++ m = a :: (l ++ m)` — *iterated `cons`*: prepend each element
of `l` onto `m`, in order.  `cons` (`a ::`) is "one more element"; on a
unit list it is "one more distinguishing", the naming event of
`seed/AXIOM/06_lens_readings.md` §6.5 (§2.4 activating once).  So `append`
is **distinguishings put in sequence** — the most primitive combine, the
floor the whole tower stands on (`theory/math/numbersystems/slot_arithmetic.md`
§1.5).

## Derivation

`append` sits *below* `+`.  `count` forgets `append`'s arrangement to give
`+`: `count (l ++ m) = count m + count l` (`UnitList.count_append`), so
`+` is `append`'s count-shadow and `append` is "`+` that still remembers
order".  That memory is visible: `append` is **not** commutative in
general — `[a] ++ [b] ≠ [b] ++ [a]` for distinguishable elements
(`UnitList.append_not_comm_general`) — and commutes *only* on units
(`UnitList.append_comm`), which is exactly where `+`'s commutativity is
born (`add_comm_from_append`).  `append` is the rung where
atom-distinguishability first becomes *visible* (order); `+` erases it.

`append` sits *above* the tree.  The free binary magma `BinTree` remembers
its bracketing (`BinTree213.node_not_assoc`); `append` is that tree
**quotiented by associativity** — the two bracketings `flatten` to the
same list (`BinTree213.flatten_assoc_collapse` *is* `append_assoc`).  So
`append` occupies one exact forgetting-level: **bracketing-blind,
order-remembering**.

`append` is linear.  Each `cons` has one tail (`ListLocate213.cons_tail_unique`)
— a unique successor — which is why strict location and order work on a
list where they fail on the branching tree.  And `append`'s co-operation
is splitting: a cut `(l1, l2)` *is* an `append`-witness, `l1 ++ l2 = l`
(`CoAppend213.mem_splits_iff`) — the inverse question read backward.

`append` is the syntactic floor.  Notation concatenates by `append`:
expressions are sequence-Raws of glyph-Raws (§6.4), so the residue's own
self-description (the glyph/print round-trip) is built on it.

## Dual function

Classical "concatenation / the free monoid" *is* `append`; 213 only names
the generator `cons` as the residue's distinguishing act, so `append` is
not a chosen algebraic structure but the operation of *continuing the
pointing*.  Its associativity — a monoid axiom classically — is here a
theorem (the tree's bracketing collapsing under `flatten`); its
non-commutativity is the visible atom-distinguishability that `count`/`+`
forgets.

## Cross-frame connections

Five readings, one floor: iterated `cons`, the free monoid, the
bracketing-quotient of the tree (`flatten_assoc_collapse`), syntactic
concatenation (§6.4), and the operation whose count is `+`
(`count_append`) and whose splits are the inverse questions
(`mem_splits_iff`).  They converge — sequencing distinguishings *is* the
free monoid *is* the order-remembering floor *is* concatenating notation.

## Open frontier

None below it that is a *problem*: below `append`/`cons` there is only the
single distinguishing act (§2.4 / §6.5), the residue pointing at itself.
That is the no-exterior bottom — not an open brick but the floor with no
simpler-than-itself version beneath.  Everything upward (`+`, `×`, `^`,
the cuts) is `append` read through one more forgetting Lens.
