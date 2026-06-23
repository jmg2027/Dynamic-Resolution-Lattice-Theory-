# What is counting, in 213?

Counting is a **Lens** — the count-reading `Raw → ℕ` — and a *cardinality* is
that reading applied to a **finite residue**.  Nothing is tallied "out there";
the number is what the count-Lens returns when it points at a finitely-presented
residue.

## 213-native answer

The count-Lens is `value = Lens.leaves.view`, the catamorphism that folds a
distinguishing into the successor structure of `ℕ` (`seed/AXIOM/06_lens_readings.md`
§6.7; `lean/E213/Lens/ProofISADemo.lean`).  A *finite* residue is carried as a
`List`, so its cardinality is `List.length` — decidable equality, no `Fintype`,
no `Classical` (`lean/E213/Lib/Math/Combinatorics/BoolEnum.lean`: `allBoolLists n`
is the `2ⁿ` length-`n` `Bool` lists, `allBoolLists_length`, and `bcount` is the
count-Lens on that carrier).  "How many" is therefore not imported set theory; it
is one reading of the residue, and which residue you read fixes which number you
get.

## Derivation — the numbers are reads of structured residues

A **binomial** is the count-Lens reading of a *layer*.  The size-`k` subsets of
`[n]` are the length-`n` `Bool` vectors with `k` trues, and counting them returns
`C(n,k)` — and the count recursion *is* Pascal's recursion (a new point is either
omitted, a `k`-subset of the first `n`, or included, a `(k−1)`-subset):
`Sperner.layer_size : bcount (cardEq k) (allBoolLists n) = binom n k`
(`lean/E213/Lib/Math/Combinatorics/Sperner.lean`).  The binomial is not a formula
imposed on the lattice; it is what the count-Lens returns at each grade.

A **factorial** is the count of *orderings*.  Enumerating every way to list a
residue's elements returns `n!`, and the count recursion is the factorial
recursion — inserting each new head everywhere multiplies the tail's orderings by
the `|l|+1` insertion slots: `Permutations.perms_length : (perms l).length =
fact l.length` (`lean/E213/Lib/Math/Combinatorics/Permutations.lean`).  With
`mem_perms_iff` (the enumeration *is* exactly the rearrangements) and `perms_nodup`
(each once), `perms l` is the nodup list of all `n!` orderings — the same `n!` the
Leibniz determinant sums over (`Algebra/Linalg213/Permutation.lean`).  Binomial and
factorial are the same Lens read at two structures, bridged by
`Sperner.binom_mul_fact : C(n,k)·k!·(n−k)! = n!`.

The **COUNT instruction** (`seed/PROOF_ISA.md`) is counting made to *force*: read
one finite residue's cardinality two ways, and a discrepancy is a theorem.  When
the bad readings together cover fewer than all `2ⁿ` colourings, a good one is
left over — and, the carrier being finite, it is *found*, not posited
(`CountExistence.count_existence`, `deficit_exists`; `union_bound`).

## Dual function

This is *cardinality* with its set-theoretic packaging stripped: a cardinal is
not an equivalence class of equinumerous sets nor an ordinal, it is a `List.length`
— the count-Lens's value on a residue carried decidably.  And the refinement 213
adds is sharper than "there is a number": the **same** residue admits **two**
readings, and bounding either bounds the other.  That is the whole of the
double count — `Sperner.sumOver_swap` is Fubini on a `0/1` incidence matrix, the
identity that "summed by rows" and "summed by columns" are one number — so
`lym_double_count` (each chain meets the antichain ≤ once ⟹ the row-sum is
bounded) and the union bound (bad events cover few points ⟹ a point is left
over) are not two tricks but one move read from its two sides.

## Cross-frame connections

The two famous COUNT theorems are this single fact at two readings of one
incidence residue.  Erdős' `R(k,k) > N` reads the (event × colouring) matrix to
over-count coverage and finds a good colouring in the deficit
(`RamseyNamedBound.ramsey_lower` — the `K_N` edge model, where the count of edges
inside a `k`-set is itself a count-read, `pairsCount_eq : #internal = C(|S|,2)`,
again the Pascal step).  Sperner reads the (subset × chain) matrix by columns to
bound the antichain (`SpernerChains.sperner_theorem`).  Union bound and LYM are
the matrix's two readings — `pigeonhole`/union-bound is *deficit ⟹ existence*,
LYM is *per-column cap ⟹ row-sum bound* — the same cardinality comparison
mirrored.  Both share the subset count `C(N,k)` (`layer_size` / `kLayer_card`):
the binomial that reads a Boolean-lattice layer *is* the count of monochromatic
events.

One frame deeper: the count-Lens's deficit is the quantitative face of `GAP`
(`a reading does not cover its codomain`), whose qualitative face is the diagonal
— the residue distinguishable from everything enumerated, forced to exist
(`Lens/Cardinality/Cantor.lean`, `seed/AXIOM/01_residue.md` §1.0.1).  Cantor's
diagonal (a reading misses its codomain *structurally*) and Erdős' deficit (a
reading misses it *by cardinality*) are one instruction read qualitatively and
quantitatively.  Counting and the residue's own existence-forcing are the same
move at two resolutions.

## Open frontier

The count-Lens reads finite residues; the infinite ones it reads only through a
modulus or a presentation, where completability becomes an intensional invariant
(`theory/math/analysis/modulus.md`; the completability frontier).  And a
cardinality is a Lens *output*, not a universe constant: no number the count-Lens
returns is privileged (CLAUDE.md "Universe-constant framing"; the deleted
`5²⁵ = N_U` claim).  Counting tells you what a residue's chosen reading returns —
not what the residue *is*, which is outside every view's image
(`FlatOntologyClosure.object1_not_surjective`).
