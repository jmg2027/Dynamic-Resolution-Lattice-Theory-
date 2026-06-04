# G200 — action A executed: the distance-1 cross-line SEPARATE, closed ∅-axiom

Action A (`G198`/`G199`): probe the **orbit / µ-ν lift of the trace-`SEPARATE`** — the one archetype
(`ProofISALifts` A3) with a realized same-family lift precedent.  Honest framing kept throughout: per
`G197` the *uniform* trace-`SEPARATE` is `H` itself, so the deliverable is a genuine partial ∅-axiom
advance or a sharply localized boundary — **not** a solve.  Result: a real advance.

## What was proved (∅-axiom, `SternBrocotMarkov` §35)

`markovNum_children_ne` (strict ∅-axiom, `#print axioms … does not depend on any axioms`):

  > for every path `p`,  `markovNum (true :: p) ≠ markovNum (false :: p)`.

The two immediate children of **every** node carry distinct Markov numbers — uniformly over the whole
tree.  This is the **distance-1 cross-line SEPARATE**: the kernel `H` is *size*-injectivity of `markovNum`
on all pairs; this closes it for all sibling pairs.

**Why it is genuinely a fragment of `H` (not a restatement).**  `slope_path_inj` already separates
distinct paths *as slopes* — but distinct slope ⇏ distinct size, and `H` is the **size** statement.
`markovNum_children_ne` is a size separation: it does not follow from `slope_path_inj`.  It is the first
uniform size-separation across the tree's branching, the exact difficulty type of `H`.

## The mechanism — a trace monovariant (the A3 archetype biting at the base)

With `(L, R) = mInterval p`, the children are `mNode (true::p) = L²R`, `mNode (false::p) = L R²`.  The
Vieta trace recurrences (`markoff_vieta_trace(_R)`) give the exact factorisation

    tr(L²R) − tr(L R²) = (tr L − tr R) · (tr(LR) + 1).

Two ∅-axiom facts close it:
  - **`trace_lt_mediant_left/right`** — the mediant trace strictly dominates both bound traces, from
    positivity alone (`tr(LR) − tr L = L.a(R.a−1) + L.d(R.d−1) + L.b·R.c + L.c·R.b ≥ 1`).  Hence at every
    node the two bounds have **distinct trace** (`mInterval_bound_traces_ne`): one bound is always the
    previous interval's mediant, strictly bigger.
  - `tr(LR) + 1 > 0`.

So the product is nonzero (`eq_zero_of_mul_eq_zero_pos`, a pure no-zero-divisor lemma) — the children's
traces differ, hence (`mNode_shape`, `tr = 3·markovNum`) their Markov numbers differ.

This is the A3 (orbit/free-action → here, trace-monovariant) lift **realized at the base rung**: a finite
per-node structural fact (mediant trace dominance) lifted *uniformly* over all nodes — exactly the
finite→uniform shape the catalog said to look for, and it bites.

## The honest boundary (where it stops — and why)

`markovNum_children_ne` closes cross-line distance 1.  The kernel's open content is **cross-line distance
`≥ 2`**: a deep-left descendant and a deep-right descendant can interleave in size (the intra-line
monovariant `markovNum_lt_append` does not order across the fork).  At distance ≥ 2 the clean
factorisation breaks — the trace difference of two depth-`k` descendants across a fork is a higher Vieta
iterate that no longer factors through a single `(tr L − tr R)` monovariant.  This is precisely the
interleaving `G197` named; the advance sharpens the kernel from "size-injective on all pairs" to
**"size-injective on cross-line pairs at distance ≥ 2"** (distance-1 now discharged, all descent/comparable
pairs already discharged by `markovNum_lt_append`).

## Status

| Pair class | Status |
|---|---|
| comparable (one path a suffix of the other) | **closed** — `markovNum_lt_append` (strict descent) |
| cross-line distance 1 (siblings) | **closed** — `markovNum_children_ne` (this note, §35) |
| cross-line distance ≥ 2 | **open** = the residue of `H` |

A real ∅-axiom step into `H`'s own difficulty type, with the boundary now one rung sharper.

## "Do we need a new ISA?" — no.  The order-monovariant is *provably* exhausted (§36)

The natural next question: does climbing past distance 1 need a **new ISA instruction**?  Answer, now a
theorem: **no — and not because a composition is still hiding, but because the *size/order* mechanism that
closed distance 1 is provably dead past it.**

`markovNum_subtree_size_interleaves` (∅-axiom, `decide`): across the root fork the two subtrees'
Markov numbers **interleave** — `markovNum [true] = 13 < markovNum [false] = 29 < markovNum [true,true] =
34`, with `[true]`, `[true,true]` in the *left* subtree and `[false]` in the *right*.  A right-subtree
value sits strictly between two left-subtree values, so **no threshold / order-monovariant separates the
two subtrees**.  The distance-1 SEPARATE worked by order-dominance (mediant trace dominates the bounds);
that mechanism cannot be a global cross-line separator, because size is not monotone across the fork.

So the residue of `H` at distance `≥ 2` is **not size-shaped**.  It is exactly the **orbit / √(−1)
residue**: which `sqrt(-1) (mod c)` residues are realised by genuine Markov triples, uniformly in `c`
(`markov_max_unique_of_orbit`'s hypothesis `H`).  The proof-ISA already carries the correct archetype —
**ORBIT** (`ProofISALifts.lift_orbit`, the free unit-root action `root_orbit_inj`) — so no new instruction
is missing.  What is missing is the **number-theoretic realizability fact**, uniform in `c`, which *is*
Frobenius 1913.  A new ISA instruction would not conjure it; the difficulty is correctly localised, not
mis-compiled.

This is the sharp terminal reading of action A: the size route is closed at distance 1 (gained) and
*proven exhausted* past it (§36); the residue is the orbit-realizability number-theoretic statement, which
the framework already names and which is the open conjecture itself.  The next real lever is on that
orbit-realizability form (uniform-in-`c` lift of `markov_max_unique_of_orbit`'s `H`), not a new
instruction and not a size argument.

### Pointers (all ∅-axiom)
- `SternBrocotMarkov.markovNum_children_ne`, `mInterval_bound_traces_ne`, `trace_lt_mediant_left/right`
- comparable case: `SternBrocotMarkov.markovNum_lt_append`
- kernel iff: `SternBrocotMarkov.markovMaxUnique_iff_markovNum_injective`
- archetype: `Lib/Math/Foundations/ProofISALifts.lean` (A3 orbit/monovariant), `research-notes/G199`
