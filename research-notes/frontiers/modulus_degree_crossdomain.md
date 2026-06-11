# Cross-domain: the modulus-degree ladder ↔ merged main (certificate depth, clockless runs)

Two bridges surfaced by merging main (async-growth promotion + the
positivity/certificate-depth note) into the modulus-degree branch.

## Bridge 1 — modulus degree IS certificate depth, one layer up

Main's `inequalities_positivity_fold_crossdomain`: Cauchy–Schwarz is one
instruction at two **certificate depths** (depth-0 Lagrange square vs
per-rung SOS folded along an induction), and the `K_{a,b}` wide/narrow regime
split is literally that depth — "certificate depth is a property of the
pointing".  This branch: **modulus degree** counts the receipts a pointing
carries (form = 0, rate = 1, composed = receipt-of-receipt), and the
rate-carrying / rate-free divide is presentation-dependent
(`zeta3_presentation_overtakes` vs the reduced presentation).

Same invariant, two layers: at the *proof* layer the certificate's fold-depth
grades how an inequality is reached; at the *completeness* layer the
modulus's degree grades how a real is reached.  Both are Lens-properties of
the pointing with the object invariant (the inequality / the limit cut).
Candidate unification: a single "receipt depth" notion with instances
(SOS-fold depth, `Dominates_s` slack exponent, `powSched` exponent-cut) —
the graded generator (`modulus_degree_ladder.md` rung 1) would be its
completeness-layer constructor.

## Bridge 2 — `reschedule_limit_eq` is "the stage is of the run", at the real layer

Main's async-growth essay chain closed on: *run* (underdetermined inside),
*grading* (the only run-invariant) — "the stage is of the run" = the temporal
instance of "finite-state is of the pointing" = "completability is of the
presentation" (three scales, one cover-non-surjection).  This branch adds the
fourth scale, as a theorem: `ModulusComposition.reschedule_limit_eq` — any
pointwise-larger schedule carries the same limit cut.  **The modulus is of
the run; the real is the run-invariant.**  And `powSched_mono` gives the
runs an order (degree order transports to schedule order), so the
"reparameterizations of one pointing" form a graded poset over the invariant
object — exactly the async picture (many runs, one growth order) at the
`Real213` layer.

Open: state the four-scale schema once (one cover-non-surjection, instances:
stage/run, finite-state/pointing, completability/presentation,
modulus/schedule) — an essay-or-Meta candidate when a fifth instance appears.
