# The forcing chain meets the foliation — one Lens reading at two scales

Cross-domain note bridging the axiom-clarification of §3.4 and the
asynchronous-growth arc.  Both make **the same move**, one at
the axiom scale and one at the run scale; naming the shared invariant
is the point (not a bare analogy).

## The two sides

**Axiom scale** (`seed/AXIOM/03_form.md` §3.4).  The
four-clause forcing chain `1 → 2 → 3 → 4` *looks* sequential — clause
2 "after" clause 1, and so on — but all four are simultaneously
present at the act of pointing (§2.3, §5.5).  The arrows are **logical
forcing, not temporal stages**; the sequence is "the order in which an
*explanation* walks the one complete event", a Lens reading after the
fact, the same expository shadow §2.2 notes for the notation
`a`, `b`, `a/b`.

**Run scale** (`theory/essays/foundations/growth_without_a_clock.md`).  The asynchronous growth system *looks* like it proceeds in
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
what is real.  The §3.4 "expository shadow" and the growth essay's "foliation is a
convention" are the *same theorem-adjacent observation* — one
`Raw` self-pointing, two Lens readouts of "what is the order here?",
neither of which the residue itself commits to.

The grading's run-invariance (`fold_eq_depth`) is the run-scale
witness of why §3.4's clause-order is *merely* expository: a fold of
the term does not see the order the explanation imposed, exactly as
depth does not see which run produced the term.

## Third scale (2026-06-10 merge): the probe schedule is a foliation of the race

The graded-rate-generator branch supplies the same move at the **modulus
scale**, and adds the two theorems the foliation story did not have.

A probe schedule `ρ : ℕ → ℕ` (`RateModulus.HtelS`, `RateStratification.DominatesS`)
is precisely a **simultaneity convention between probe resolution and layer
time**: "probe denominator `k` is admitted at layer `i₀`" (`k ≤ ρ i₀`) is the
foliation leaf pairing the two clocks.  The run-invariant is the cut — the
real does not move under rescheduling (`rcut_rescale`,
`modulus_rescale_invariant`, `reschedule_limit_eq`; the stage is of the run,
already the fourth scale in `modulus_degree_crossdomain.md`).  What the merge
makes visible:

  1. **The foliation-freedom has a proven boundary.**  Main's arc says the
     foliation is a convention; this branch proves there are objects for
     which *no* convention in an entire class closes the race —
     `wallis_no_graded_certificate`: the Wallis pointing of π/2 defeats
     **every** positive schedule (rung ∞).  "Any foliation will do" is
     pointing-relative; some pointings out-run the whole foliation family.
  2. **Foliations are not totally ordered.**  When does one simultaneity
     convention dominate another?  Exactly the schedule comparison law:
     `dominatesS_schedule_mono` (the gap law `1/ρ' − 1/ρ` non-increasing is
     the sufficient condition) and `schedule_comparison_needs_gap` (the gap
     law is indispensable — pointwise the ladder is **not a chain**).  The
     foliation poset of a race is a genuine partial order with proven
     incomparabilities, witnessed by `decide` at layer 2.

So the table gains a row: at the modulus scale the apparent sequence is the
schedule's admission ladder, and what is actually there is the cut (the
presentation-invariant real).  The §3.4/§6.6 reading persists: the rung is a
Lens-grading of *pointings*; the residue sits in no rung.

## Status

Closed on both sides (both chapters are permanent, both cite ∅-axiom
Lean).  This note records the bridge; the natural home if it earns an
essay is the foundations cluster ("the expository sequence is a Lens
reading" as a standalone synthesis spanning §3.4 + the growth essay).
No open Lean obligation — the connection is conceptual and already
witnessed by `fold_eq_depth` (run-invariance) + the §3.4 prose.
