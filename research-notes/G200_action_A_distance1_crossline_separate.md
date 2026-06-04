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

A real ∅-axiom step into `H`'s own difficulty type, with the boundary now one rung sharper.  Next probe:
whether a *bounded-distance* induction (distance `k` ⟹ distance `k+1`, the LOOP archetype) or a
value-window monovariant can climb past distance 1 — or whether distance 2 already carries the full
interleaving (a focused `decide`-survey of distance-2 cross pairs would test which).

### Pointers (all ∅-axiom)
- `SternBrocotMarkov.markovNum_children_ne`, `mInterval_bound_traces_ne`, `trace_lt_mediant_left/right`
- comparable case: `SternBrocotMarkov.markovNum_lt_append`
- kernel iff: `SternBrocotMarkov.markovMaxUnique_iff_markovNum_injective`
- archetype: `Lib/Math/Foundations/ProofISALifts.lean` (A3 orbit/monovariant), `research-notes/G199`
