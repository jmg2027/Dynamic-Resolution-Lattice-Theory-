# The forcing chain meets the foliation — one Lens reading at two scales

Cross-domain note bridging this branch's axiom-clarification work and
main's asynchronous-growth arc.  Both make **the same move**, one at
the axiom scale and one at the run scale; naming the shared invariant
is the point (not a bare analogy).

## The two sides

**Axiom scale** (`seed/AXIOM/03_form.md` §3.4, this branch).  The
four-clause forcing chain `1 → 2 → 3 → 4` *looks* sequential — clause
2 "after" clause 1, and so on — but all four are simultaneously
present at the act of pointing (§2.3, §5.5).  The arrows are **logical
forcing, not temporal stages**; the sequence is "the order in which an
*explanation* walks the one complete event", a Lens reading after the
fact, the same expository shadow §2.2 notes for the notation
`a`, `b`, `a/b`.

**Run scale** (`theory/essays/foundations/growth_without_a_clock.md`,
main).  The asynchronous growth system *looks* like it proceeds in
stages — "stage n completes, then stage n+1".  But that lockstep is a
**foliation**: a simultaneity convention, a Lens choice, not a fact
(`Theory/Raw/Async`, `level3_diverges` — two runs reach snapshots that
disagree even after a global swap).  What survives run choice is only
the **grading** — depth/leaves as catamorphisms of the term itself
(`Levels.fold_eq_depth`, `fold_eq_leaves`), the DAG cost
(`RawDagSize.dagSize`).  "When" collapses into "what".

## The shared invariant

Both are the **state-transition = state** non-separation of
`seed/AXIOM/06_lens_readings.md` §6.6, forced by the absence of an
external time axis (§5.7, frozen/dynamic), read at two granularities:

| | the apparent sequence | what is actually there |
|---|---|---|
| axiom §3.4 | the 1→2→3→4 forcing chain | one complete pointing act |
| run (growth essay) | the stage-n-then-n+1 foliation | the graded term (run-invariant fold) |

The apparent sequence is, in both cases, **an expository / foliation
Lens reading**; the object (the completed act / the graded term) is
what is real.  My §3.4 "expository shadow" and main's "foliation is a
convention" are the *same theorem-adjacent observation* — one
`Raw` self-pointing, two Lens readouts of "what is the order here?",
neither of which the residue itself commits to.

The grading's run-invariance (main, `fold_eq_depth`) is the run-scale
witness of why §3.4's clause-order is *merely* expository: a fold of
the term does not see the order the explanation imposed, exactly as
depth does not see which run produced the term.

## Status

Closed on both sides (both chapters are permanent, both cite ∅-axiom
Lean).  This note records the bridge; the natural home if it earns an
essay is the foundations cluster ("the expository sequence is a Lens
reading" as a standalone synthesis spanning §3.4 + the growth essay).
No open Lean obligation — the connection is conceptual and already
witnessed by `fold_eq_depth` (run-invariance) + the §3.4 prose.
