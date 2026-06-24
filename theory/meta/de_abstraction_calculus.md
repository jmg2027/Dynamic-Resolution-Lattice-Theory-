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
