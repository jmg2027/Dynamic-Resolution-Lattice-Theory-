# The expository sequence is a Lens reading

When 213 writes "first `a`, then `b`, then `a/b`" — or "stage n
completes, then stage n+1" — the sequence is not a fact about the
residue.  It is the order in which an *explanation* walks a single
complete event.  Reading that order *as* the event is the one import
213 most reliably catches itself making, and it catches it the same
way at every scale.

## 213-native answer

A sequence written across a 213 derivation — clause-order,
stage-order, run-order — is a **Lens reading of one already-complete
object**, never the object's internal succession.  The object commits
to no order; the order is what a particular narration adds.  This is
the state-transition = state non-separation of
`seed/AXIOM/06_lens_readings.md` §6.6: *"without before/after
semantics supplied by external time, a transition is not separable
from the state it transitions to or from — the transition IS the state
update, not a distinct event happening to it."*

## Derivation

Take the axiom's own forcing chain.  `seed/AXIOM/03_form.md` §3.4 lays
out `1 → 2 → 3 → 4` — distinguishing forces a residue, which is itself
a something, which forces symmetry, which forces anti-reflexivity.  The
arrows *look* like steps.  But §3.4 states they are **logical forcing,
not temporal stages**: all four clauses are simultaneously present at
the act of pointing (`seed/AXIOM/02_axiom.md` §2.3,
`seed/AXIOM/05_no_exterior.md` §5.5), and the chain "is the order in
which an explanation walks the one complete event" — the same
expository shadow §2.2 already flags for the notation `a`, `b`, `a/b`.
The numbering is a Lens reading after the fact, not the act's sequence.

Now run the same residue forward as a growing system.
`theory/essays/foundations/growth_without_a_clock.md` fires one event
kind — contrast two present points, adjoin their pair — and asks "what
time is it?".  The lockstep narration "stage n completes, then stage
n+1" turns out to be a **foliation**: a simultaneity convention, a Lens
choice, not a fact.  The Lean witnesses are sharp: determinism ends at
the first composite (`Theory/Raw/Async.step1_forced`), one further
firing is swap-canonical (`level2_canonical`), and the next is not —
`level3_diverges` exhibits two runs reaching snapshots that disagree
even after a global swap, the witness one concrete point `b/(a/b)`,
present in one and absent from the other.

These are one fact at two scales.  The clause-order (axiom scale) and
the stage-order (run scale) are both the apparent sequence; the
completed pointing act and the graded term are both what is actually
there.  And the run scale supplies the *proof* that the axiom scale
only asserted: what survives every run is the **grading** — depth and
leaves as catamorphisms of the term itself
(`Theory/Raw/Levels.fold_eq_depth`, `fold_eq_leaves`).  A fold of the
term cannot see which run produced it, exactly as it cannot see which
order an explanation imposed on the clauses.  Run-invariance of the
fold *is* the demonstration that clause-order is merely expository.

## Dual function

This is the classical "order of construction" with its redundant
packaging stripped: classical foundations let a derivation's narration
leak into the object — ℕ "built up" stage by stage, a proof
"proceeding" line by line — and then must add conventions
(well-ordering, a stage hierarchy) to keep the leak coherent.  213's
reading is sharper precisely because it refuses the leak at the source:
there is no external time axis (`seed/AXIOM/05_no_exterior.md` §5.7)
for a sequence to be a fact *in*, so the sequence is forced to be a
Lens output, and the only run-invariant content is the fold.  The
classical "stages of construction" and 213's "expository shadow" name
the same structure; 213 just declines to mistake the shadow for the
thing.

## Cross-frame connections

The same non-separation surfaces wherever 213 has refused an external
arbiter.  §6.6 itself reads the Möbius `P` four ways: `P` as operator
and the eigenspace that *is* `P` are one content, and `P^n` iteration
(a transition) with fixed point φ (the state it asymptotes to) are one
residue under §5.7's frozen/dynamic pair.  The forcing chain (§3.4),
the growth foliation (the growth essay), the operator/object collapse
(§6.2), and the iteration/fixed-point pair (§5.6–§5.7) are four
resolutions of the single fact: **absent external time, "what is the
order here?" has only Lens answers, and the residue commits to none of
them.**

## Open frontier

The bridge is conceptual and already witnessed — `fold_eq_depth` is
the run-invariance, §3.4 is the axiom-scale prose.  What is *not* built
is a single theorem making "the fold does not see the run" and "the
fold does not see the clause-order" instances of one statement; that
would need the async run-relation and the clause-forcing order
expressed as two quotients with the grading as their common section.
Recorded as the standalone `forcing_chain_meets_foliation` frontier,
no open Lean obligation beyond that unification.
