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

The generic ∅-axiom `List` lemmas this builds on — `mem_map_of_mem`,
`exists_of_mem_map`, `mem_append_*`, `mem_flatMap_*`, `nodup_append`,
`nodup_map_of_inj`, `map_congr` / `map_eq_comp`, `getD_*`, `list_ext_getD`,
the `filter` lemmas, and the nodup-cardinality comparison
(`nodup_length_le_of_subset`, `nodup_length_eq_of_mem_iff`) — live in
`lean/E213/Meta/Tactic/List213.lean` (the propext-free `List` library), so
they are reusable across the whole repo, not just here.

## Counting (count-Lens b₀ = 1)

On top of the enumeration, a hand-rolled count `bcount` (own definition —
core `List.countP` lemmas carry `propext`; uses the `Bool` conditional
`bif`, which reduces by `rfl`) with its `append` / `map` / `congr` /
always-false lemmas gives:

  - `bcount_allFalse` / `bcount_allTrue` — exactly **one** length-`n`
    list is all-`false` (resp. all-`true`);
  - `bcount_const` — exactly **two** colourings of each nonempty length
    are constant.

`bcount_const` is the **division-free, universal, ∅-axiom count-Lens
form of `b₀ = 1`**: a cochain lies in the δ⁰-kernel of a connected
`K_{NS,NT}^{(c)}` iff it is constant (`KernelConstancyUniversal.
isKer_iff_const`), so the constant-list count `= 2` is `|ker δ⁰| = 2`
for every nonempty deployment at once — where the existing
`kerSizeDelta0Direct = 2` is `decide`-only (its binary decode pulls core
`Nat.div`).

## Role

This is the cardinality base for counting `Bool`-cochain subsets without
`decide`-per-instance.  The structural kernel result is already closed;
`bcount_const` supplies its count form.  Downstream it underwrites the
first Betti number of the bipartite cohomology (`|im δ⁰| = 2^(V−1)` by
fiber counting over the enumeration).

## Connection

- `theory/math/combinatorics/graph_connectivity.md` — the structural
  δ⁰-kernel = constants result this would count
- `theory/math/numbertheory/euclidean_division.md` — companion native
  primitive, same ∅-axiom-by-design motivation (core `Nat.div` propext)
- `lean/E213/Meta/Tactic/List213.lean` — the ∅-axiom `List` length lemmas
  this builds on
