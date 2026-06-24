# The de-abstraction calculus — atomic moves of the 0-axiom peel

**Thesis.**  The point of the strict 0-axiom discipline is not hygiene.  An axiom — or
a Mathlib asset, or any abstraction — is a *frozen mechanism*: a record of distinguishing-acts
folded shut and given a convenient name.  Invoking the name uses the mechanism without seeing
it; the convenience *is* the blindness.  Peeling a result down to ∅-axiom thaws the freeze and
exposes the mechanism — the **essence** the abstraction hid.

But the peel itself is the deeper object.  It *looks* like drudgery (노가다); that appearance
is the peel seen at low resolution — undifferentiated only because un-analysed.  Raise the
resolution on the peel and it is not one thing but a small set of **atomic de-abstraction
moves**, each of which reveals a *different* fact about the abstraction.  Cataloguing those
moves — not any single essence — is the general instrument, because the taxonomy transfers
across all of mathematics where any one essence is a single datum.

This file is that catalogue, abstracted from the de-abstraction work it documents (the
∅-axiom cohomology + number-theory build: `Cohomology/{DeltaSqZero,Examples/ColexRoundTrip,
Examples/XorInvolution}`, `NumberTheory/{MulDescentRec,FactorizationCarrier}`).  Every
archetype is pinned to verified instances — no move is admitted that cannot be exhibited.

## The four moves

Each move is named, given **what it reveals**, and grounded in concrete dirty→pure (or
opaque→transparent) instances from the corpus.

### ① Substitute — pure witness for a propext-dirty convenience

A stdlib lemma routes through `propext` / `Quot.sound` (typically an `↔`, a quotient, or a
typeclass instance); replace it with an axiom-free witness of the same fact.

| dirty convenience | hidden axiom | pure witness |
|---|---|---|
| `LawfulBEq (List Nat)` (`beq_self_eq_true`, `eq_of_beq`) | propext + Quot.sound | decide-route via `instBEqOfDecidableEq` (`ColexRoundTrip.nat_beq_refl`, `list_beq_false_of_ne`) |
| `Nat.lt_one_iff` | propext (↔) | `ColexRoundTrip.lt_one_eq_zero` |
| `Nat.succ_ne_zero` | propext | `Nat.noConfusion` (`MulDescentRec`) |
| `Nat.sub_add_cancel` | propext | `NatHelper.sub_add_cancel` |
| `Prod.mk.injEq` | propext (↔) | `congrArg Prod.snd` (`DeltaSqZero.gridList_nodup`) |

**Reveals**: *where classical content is smuggled into "elementary" results.*  That `δ²=0`
and the colex bijection need **zero** propext is invisible from the statements; the substitution
moves draw the exact propext boundary — and show which naïve formalisations would have crossed it.

### ② Translate — opaque form → transparent form that surfaces the mechanism

Re-express a convenient-but-folded definition so its mechanism is on the surface.

| opaque form | transparent form | what surfaces |
|---|---|---|
| `deltaAt`'s dependent-`if` `List.foldl` | guard-free `xorFold` via `cochainAtNat` (`DeltaSqZero.deltaAt_eq_xorFold`) | the boundary sums **only valid faces**; out-of-range terms are genuinely `0` (= the `else`), not silently excluded by a `Finset.sum`'s index set |
| `List.foldl xor false` | `xorFold` (`DeltaSqZero.foldl_xor_false`) | the fold *is* a ℤ/2 sum; left-fold accumulator is inessential |

**Reveals**: *what the convenience folded away.*  The `if`-guard hid that the coboundary's
domain is exactly the valid faces; translating it out makes "what is summed and what is not"
fully explicit.

### ③ Bridge — explicit construction of what the abstraction supplied for free

The abstraction silently provided connective tissue; build it by hand, and the construction
*is* the abstraction's actual content.

| free-from-abstraction | explicit bridge | what it presupposed |
|---|---|---|
| "the k-subsets of `{0..n−1}`" | the colex bijection `kSubset ↔ subsetIdx` (`ColexRoundTrip`: `kSubset_inj`, `kSubset_surj`, `subsetIdx_kSubset`, `kSubset_subsetIdx`) | a *concrete enumeration* (Pascal split) with an index inverse — "k-subset" is not primitive |
| `Finset` finiteness / `Finset.sum` | `range_nodup`, `mem_range_lt`, `gridList` + `gridList_nodup`, `xorFold_{append,map,congr}` (`DeltaSqZero`) | the Nodup/finiteness apparatus a "sum over a finite index set" assumes |
| `List.find?` correctness | first-match from `find?_cons` (`ColexRoundTrip.find?_range_eq_some`) | the search-returns-the-unique-witness fact |

**Reveals**: *what the abstraction was quietly assuming.*  "k-subset" and "finite sum" are not
atoms; the bridges expose the enumerative and finiteness machinery they compress.

### ④ Avoid — route around an irreducibly-tainted tool, revealing the alternative mechanism

Some tools cannot be made pure (they are quotient-built); refuse them and find another path.
The path found is often the *more essential* mechanism, of which the tool was a low-resolution shadow.

| avoided tool | hidden axiom | route taken | shadow exposed |
|---|---|---|---|
| `List.Perm` / `List.erase` | propext + Quot.sound | `filter`-based pair removal (`XorInvolution.xorFold_involution`) | "permutation invariance" is the shadow of a **concrete matching** (the filter-pairing) |
| `List.range_succ`, `mem_range`, `find?_append`, `find?_eq_none` | propext (+ Quot) | rebuilt from `find?_cons` + `range.loop` unrolling (`ColexRoundTrip`) | the cons/append recursion the quotient form hides |

**Reveals**: *what is irreducibly classical vs what has a constructive substitute* — and when a
"convenient invariance" was standing in for a buildable construction.

## How the moves build the lattice

A result's **removal-fingerprint** — which moves its peel required, in what order, bottoming out
in which kernel fact — is a measurement of its internal mechanism.  Results that look unrelated
at the abstract top, but share a fingerprint, are *the same thing at resolution-bottom*.  These
shared bottoms are the lattice's edges, and they are **invisible from the abstract forms** — only
the peel exposes them.

**Worked edge (this corpus).**  `Cantor / the residue` (`object1_not_surjective`,
`OneDiagonal.reentry_one_nonclosure`) and `δ²=0` (`DeltaSqZero.delta_sq_zero_general`) appear
unrelated — one a limitative theorem, one a chain-complex law.  Peel both and they bottom out in
the **two faces of the one Bool distinguishing**:

- `!b ≠ b` (`bnot_self_ne`) — the two elements are *distinguished* → a fixed-point-free map on the
  value space → Lawvere diagonal → **a residue is forced** (non-surjectivity);
- `xor b b = false` (`XorInvolution.xor_self`) — a thing is *not distinguished from itself*, leaves
  no difference → a fixed-point-free involution on the index space pairs every value → **cancellation
  is forced** (`δ²=0`).

"`2` differs from `2`'s negation" and "`2` equals itself" — the minimal distinguishing's two faces
— are the bottoms of, respectively, *residue-forced* and *cancellation-forced*.  Same primitive,
dual consequence.  No reading of "Cantor's theorem" against "chain complex δ²=0" yields this edge;
the removal-trajectory does.

**A third node, machine-checked (the program *run*).**
`Cohomology/Examples/EvenCardCancel.lean`: "a non-empty power set has an even number of
elements" (`xorFold (fun _ => true) (range (m+m)) = false`, `even_card_cancel`).  Abstractly
*combinatorics / parity* — no visible tie to a chain-complex law.  Peeled, it bottoms out in a
**fixed-point-free halving involution** `code ↦ code ± m` (the high-half `not`), fed to the
**same** `xorFold_involution` engine as `δ²=0`.  So three results unrelated at the top — the
residue, `δ²=0`, even-cardinality cancellation — share one bottom: a fixed-point-free involution
on the one distinguishing.  The edge is now a verified node, not a claim.

*Meta-evidence the calculus is real*: building that node **live-surfaced a Substitute move** —
`Nat.add_left_cancel` (propext) had to be swapped for `Nat.ne_of_lt ∘ Nat.lt_add_of_pos_right`
(pure).  The taxonomy predicted the move before the peel produced it.

## The lattice's three bottoms — the distinguishing's three atom-readings

Not everything shares cluster A's bottom; that is the point of a *lattice*.  The
**removal-fingerprint discriminates**, and the bottoms so far reached are exactly the three
readings of an atom — the count-Lens facets (`seed/AXIOM/06_lens_readings.md`):

| cluster | atom | kernel | engine | reading | nodes |
|---|---|---|---|---|---|
| **A** | `Bool` | `xor b b = false` / `!b ≠ b` | `XorInvolution.xorFold_involution` | atoms **distinguished** (parity, fixed-point-free involution) | residue (`object1_not_surjective`), `δ²=0` (`delta_sq_zero_general`), even cardinality (`even_card_cancel`) |
| **B** | `ℕ` (`succ`) | `Nat.rec` (structural) | `Foundations.MeasureInduction.measureInduction` | atoms **counted / ordered** (measure-descent) | FTA *existence* (`mulDescentRec`), Raw descent (`no_infinite_descent`), `Ω`-descent |
| **C** | `Unit` | `() = ()` | (genesis) `UnitList.append_comm` / `list_unit_determined_by_length` | atoms **undistinguished** (count is the complete invariant) | `(ℕ,+)` from `List Unit`, `+`-commutativity, `list_unit_determined_by_length` |

The fingerprint tells these apart where the abstract forms ("Cantor", "FTA", "δ²=0", "even
cardinality", "commutativity") do not.  And the three are dual/complementary at the **atom**:
A's `Bool` *distinguishes* its two atoms (`!b ≠ b`), C's `Unit` does *not* (`() = ()`), and B's
`ℕ` *counts* them (`succ`).  (Cluster A itself refines into A.i parity and A.ii separation — see
*Cluster A is not atomic* under *Composite edges*; the table's A row is the union of both sub-facets.)

**The lattice's floor is the distinguishing, at its three atom-readings.**  And there is
nothing below the distinguishing to land on: every peel terminates in one of these atom-readings
(or a composite), because the distinguishing is the floor (`seed/AXIOM/01_residue.md` §1.3).

**A refuted prediction (the instrument falsifying, not confirming).**  The first draft claimed
`measureInduction` (structural `Nat.rec`) *drops a CIC fragment* versus the corpus's
`Nat.strongRecOn`, which as a *constant* is EXTENDED-FRAGMENT (`Acc.rec`, `WellFounded.rec`).
Running `cic_footprint` on actual corpus descent proofs **refuted this**: `OddPartDecomposition.
decomp_and_odd` and `stripTwo_fuel_eq` use `induction … using Nat.strongRecOn` yet measure
**MINIMAL-STRUCTURAL** (`recursors []`) — Lean's equation compiler emits structural `brecOn`
code and never pulls the `Nat.strongRecOn` constant (with its `Acc.rec`) into the closure.  So
there is **no footprint drop**; `measureInduction`'s value is solely as a reusable, explicitly
structural engine *naming* cluster B's bottom, not as a footprint improvement.  Recorded because
the instrument caught the overclaim — the unfold-test applied to a claim about the tool itself.

## Composite edges — clusters combine

The clusters are not disjoint; a single result can draw on several, and that *combination* is a
lattice edge between them.  The clearest case in this corpus is `delta_sq_zero_general` itself:
its **cancellation** is cluster A (`xorFold_involution`, the order-swap fixed-point-free
involution), but it sits **on top of** cluster B — the colex bijection (`kSubset_inj`,
`kSubset_surj`, `subsetIdx_kSubset`, …) it needs to collapse the faces is proved by *structural
induction on the dimension `n`* (the `Nat.rec` bottom).  So `δ²=0` is an **A-over-B composite**:
a parity cancellation carried over a counted/structural foundation.  (`cic_footprint`:
MINIMAL-STRUCTURAL, TIER-A — both ingredients present, both pure.)  Reading a proof's fingerprint
this way says *which* bottoms it stands on and *how they stack* — finer than placing it in a
single cluster.

**FTA — the branch namesake — is the dual composite.**  `fta_existence_and_count`
(`NumberTheory/MulDescentRec`, `FTAUniqueness`) peels into two halves with *different* bottoms:

- **existence** (`mulDescentRec`, every `n ≥ 2` has a prime factorization) bottoms in cluster B —
  peel `n ↦ n / minFac n`, recurse on the strictly-decreasing `Ω`-count (`measureInduction`);
- **uniqueness** (`factorization_unique`: two prime lists with equal product have equal occurrence
  count at every prime) bottoms **not in an involution** but in `vp_prodL_eq_countOcc` →
  `vp_prime_single` (`vp q p = if p = q then 1 else 0`) → `prime_not_dvd_prime` (distinct primes
  don't divide each other).  Its kernel is the **injectivity/separation** of distinct atoms: each
  prime's valuation is independent, so the multiplicities are *read off the product* and the two
  lists are forced equal.

So FTA is a **B-then-A composite** — the mirror of `δ²=0`'s **A-over-B**.  Both stack a cluster-A
consequence on a cluster-B (descent) foundation; they differ in *which* A-facet sits on top.

### Cluster A is not atomic — parity vs. separation

The two composites force a refinement the single-bottom table hid.  Cluster A's reading "atoms
**distinguished**" splits by **how the distinction is used**, and the unfold-test confirms the two
are operationally different moves, not one relabelled:

| sub-facet | kernel | engine | how the distinction is used | nodes |
|---|---|---|---|---|
| **A.i** parity / involution | `xor b b = false` | `XorInvolution.xorFold_involution` | a fixed-point-free **pairing** cancels matched terms → *cancellation forced* | residue, `δ²=0`, even cardinality |
| **A.ii** separation / injectivity | `vp_prime_single` / `prime_not_dvd_prime` (`p = q` decidable on `ℕ`) | `FTAUniqueness.vp_prodL_eq_countOcc` | distinct atoms are **told apart and counted independently** → *readout / uniqueness forced* | FTA uniqueness (`factorization_unique`), `vp` prime-separation |

Both rest on the one Bool distinguishing at the very bottom (A.ii's `if p = q` *is* `Nat.decEq`,
the distinguishing read on `ℕ`).  But A.i *pairs to annihilate* while A.ii *separates to read off*:
inverse uses of the same primitive.  Unfold-test: the two cash out to different engines
(`xorFold_involution` vs. `vp_prodL_eq_countOcc`) and different forced consequences
(cancellation vs. uniqueness) — so the refinement is operational, admitted; A is a sub-lattice, not
a point.

The symmetry that earns the refinement: **`δ²=0` = A.i-over-B, FTA = A.ii-over-B** — two
descent-composites distinguished only by which A-facet rides the descent.  The lattice's edges are
now between *sub*-facets, exactly as the unfold-test licenses each split.

### B is the universal carrier — cluster C rides it too

The same fingerprint applied to cluster C closes the pattern.  `list_unit_determined_by_length`
(`Foundations.IndistinguishableAtom`, "equal length ⟹ equal unit-list") peels into: a **structural
recursion** `list_unit_determined_by_length as bs` (B-descent on the list) bottoming in `cases a;
cases b ⟹ () = ()` (C's kernel, the undistinguished atom).  So **C-over-B** — count-completeness
*forced by* structural descent.

All three facet-consequences therefore ride the **same** B foundation:

| composite | top facet | what descent forces |
|---|---|---|
| `δ²=0` (`delta_sq_zero_general`) | **A.i** parity | cancellation |
| FTA uniqueness (`factorization_unique`) | **A.ii** separation | uniqueness |
| `list_unit_determined_by_length` | **C** count | count-completeness |

**B is the universal carrier**: A.i, A.ii, C are not three independent floors but three things
structural descent *delivers* — what's forced at the bottom of a count, read three ways.  (The pure
*kernel* nodes — `xor_self`, `vp_prime_single`, `() = ()` — are A.i/A.ii/C standing alone, no
descent; the *theorems* that put them to work all ride B.)

### A.i presupposes A.ii — a directed edge inside the engine

The two A-facets are not even parallel.  `XorInvolution.xorFold_involution` — A.i's engine — carries
`hnodup : l.Nodup` as a **load-bearing** hypothesis: `filter_eq_singleton` needs it so each element
filters to exactly `[x]`, i.e. the fixed-point-free pairing annihilates only because every element
occurs **once**.  `Nodup` is built from `DecidableEq` — *exactly* A.ii's kernel (`if p = q`).  So the
**parity-cancellation (A.i) presupposes separation (A.ii)**: a directed edge A.i ⟹ A.ii, not a
symmetric pair.

This in turn splits A.i and explains the original residue/`δ²=0` "two faces":

- **A.i-diagonal** (the residue, `object1_not_surjective`): a fixed-point-free map on `Raw → Bool`
  → diagonal → non-surjectivity.  Lives on a function space — **no finite list, so no `Nodup`
  possible**: A.ii-free.
- **A.i-pairing** (`δ²=0`, even cardinality): a fixed-point-free **involution over a `Nodup` list**
  → cancellation.  **A.ii-coupled** (needs separation).

So "`!b ≠ b`" (the diagonal face) is A.ii-free and "`xor b b`" (the pairing face) is A.ii-coupled —
which is *why* the residue and `δ²=0`, both bottoming in the one Bool distinguishing, occupy
different lattice positions.  The earlier "dual consequence of one primitive" finding is sharpened:
the dual is *diagonal vs. pairing*, and only the pairing leg carries the separation edge.

## The stopping criterion (against infinite regress)

Analysing the peel is itself a peel (de-abstracting the abstraction "노가다"), so it can recurse
without end.  It is grounded by the **unfold-test**: descend a level only while it yields an
*operational* distinction — a new move, a new tool, a new lattice edge.  When a level stops
producing operational distinctions, that is the working resolution; recursing further is fog, not
depth.  (Same discipline as the *Fog jargon* failure-mode: a distinction is real iff it cashes out.)

## Relation to the existing instrumentation

The corpus already measures the *trajectory*; this catalogue names the *moves*:

- [`forcing_versus_bookkeeping.md`](forcing_versus_bookkeeping.md) — the companion: *when* a
  ∅-axiom proof is forced to be structurally revealing vs. mere bookkeeping (the three veins).
  This file is the dual: the *atomic moves* such a revealing peel decomposes into.
- `tools/scan_axioms.py`, `tools/cic_footprint.py` — measure what a peel leaves and uses (the
  fingerprint readout).
- `seed/META_SCAN_ARCHETYPES.md` — reusable scanner archetypes (find peel-candidates).
- The CLAUDE.md failure-mode catalogue — a *documented trajectory of conceptual de-abstractions*
  (the same instrument, one level up: peeling imported frames off the prose).

This file is the missing piece: the taxonomy of de-abstraction *moves*, so the trajectory data
those tools produce can be read structurally and the lattice edges named.

## Honest status

First articulation, abstracted from one body of de-abstraction work (the ∅-axiom cohomology +
number-theory build).  The four moves are *facts about how that work went*, each exhibited — not
hypotheses.  The taxonomy is extensible and falsifiable: a future peel that needs a move not
reducible to substitute / translate / bridge / avoid extends the catalogue; the unfold-test keeps
it operational.  The lattice it is meant to build is the genuinely open program — this names the
tool, not the finished map.
