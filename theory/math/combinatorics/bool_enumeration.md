# Finite Bool-cardinality enumeration

**Status**: Closed.

## Why a native enumeration

Mathlib-free core Lean has no `Fintype` / `Finset.card`, and its `List`
membership / `Nodup` lemmas (`List.mem_map`, `List.mem_append`,
`List.nodup_append`, `List.nodup_cons`) carry `propext`.  So a strict
∅-axiom finite-cardinality argument over `Bool`-valued data has nothing
to stand on — it must enumerate by hand.

The carrier is **`List Bool`, not `Fin n → Bool`**, chosen deliberately:

  - equality of cochains is decidable **list** equality — no `funext`
    (which would route through `Quot.sound`);
  - the count is `List.length` — no `Fintype.card`;
  - the enumeration is structural recursion — no division (the binary
    decode `i ↦ i / 2^j % 2` used by `decide`-based counts pulls core
    `Nat.div`, which carries `propext`).

## Content

`lean/E213/Lib/Math/Combinatorics/BoolEnum.lean` (∅-axiom):

  - `allBoolLists n` — all `2^n` length-`n` Bool lists, built by
    prepending `false` / `true` to each length-`(n−1)` list;
  - `allBoolLists_length` — `|allBoolLists n| = 2^n` (via the ∅-axiom
    `List213.length_append` / `length_map`);
  - `mem_allBoolLists` — completeness: every length-`n` Bool list occurs;
  - `length_of_mem_allBoolLists` — every entry has length `n`;
  - `nodup_allBoolLists` — no duplicates.

Together: `allBoolLists n` is a finite carrier of exact, ∅-axiom
cardinality `2^n`, with completeness and no overcounting.

## Pure `List` toolkit

To stay ∅-axiom the file re-proves, by structural induction, the `List`
lemmas whose core versions carry `propext`:

  - `mem_map_of_mem`, `exists_of_mem_map`,
  - `mem_append_left`, `mem_append_right`, `mem_append_iff`,
  - `nodup_append` (disjoint append), `nodup_map_cons` (injective cons).

These are reusable for any finite-Bool counting argument.

## Role

This is the cardinality base for counting `Bool`-cochain subsets without
`decide`-per-instance — e.g. a division-free universal count of the
δ⁰-kernel (`= 2`, the count-Lens reading of the structural
`KernelConstancyUniversal` result), and downstream the first Betti
number of the bipartite cohomology.  The structural kernel result is
already closed; this supplies the finite-cardinality machinery a
count-form statement needs.

## Connection

- `theory/math/combinatorics/graph_connectivity.md` — the structural
  δ⁰-kernel = constants result this would count
- `theory/math/numbertheory/euclidean_division.md` — companion native
  primitive, same ∅-axiom-by-design motivation (core `Nat.div` propext)
- `lean/E213/Meta/Tactic/List213.lean` — the ∅-axiom `List` length lemmas
  this builds on
