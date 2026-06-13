# G169 — intensional completability: the presentation/real split, and the conjectures it opens

**Date**: 2026-06-01.  **Status**: research directions + supporting ∅-axiom lemmas.
**Source of truth**: `lean/E213/Lib/Math/Real213/Completability/IntensionalCompletability.lean`
(3 PURE / 0 DIRTY).  **Anchors**: `Real213/{PresentationDependence, CrossDetOvertake,
CrossDetEqDenom, CrossDetConstDenom, GeometricThreshold, RateStratification}`,
`Cauchy/DepthOverflowDuality`, the original transfinite-ordinals proposal ("내포적 환원").

## The hinge that opens this

`PresentationDependence` proved a sharp fact: the cut `rcut` is invariant under
rescaling `(a,d) ↦ (c·a, c·d)`, but the completability bridge `CrossDetSmall` is not
(cross-det scales `c²`, denominator `c`).  So the W-vs-d comparison — the whole
tower-native completeness program (T1–T4) — is a test that reads the **presentation**,
not the **real**.  That is exactly the original proposal's *intensional reduction*
posture: the extensional readout (a coordinate of a chosen num/den) versus the
intensional invariant (the real itself, the cut).

This note records what that split makes conjecturable, and backs the first step with
∅-axiom lemmas rather than leaving it as prose.

## Closed this step (the precise content of the split)

  - **`crossDetSmall_rescale_antitone`** — rescaling **up** only **loses** the bridge:
    `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d` for `c ≥ 1`.  The smallness
    condition is monotone *down* the rescaling order, so the **gcd-reduced presentation
    is the canonical place to apply it**: a real that fails the bridge at its reduced
    form cannot be rescued by scaling up, and one that passes (after the `c`-cancellation)
    passes at the reduced form.
  - **`modulus_rescale_invariant`** — the **completion itself** is presentation-invariant:
    a total modulus for `a/d` is, verbatim, a total modulus for `(c·a)/(c·d)` (the cut is
    unchanged).  Whether a real completes is a property of the cut.
  - **`completability_is_intensional`** — the two together: the *test* is
    presentation-relative (antitone), the *truth* is presentation-invariant.

So the W-vs-d apparatus is an extensional probe; the intensional content is the cut's
completion, and the reduced presentation is the canonical probe point.

## Conjectures (the research directions)

### C1 — the intensional completability invariant is the ∃-closure over presentations

`CrossDetSmall a/d` is *sufficient* for completion but presentation-relative.  The
intensional ("does the real complete?") question should be the **existential closure**:

> **C1.**  A cut completes (has a total modulus at every `(m,k)`) iff *some* monotone
> convergent presentation of it satisfies `Htel` (equivalently, is dominated at every
> layer, `RateStratification.htel_iff_dominates`).

`modulus_rescale_invariant` is one direction's stability (rescaling preserves the
witness's completion); `crossDetSmall_rescale_antitone` says the witness can be taken
reduced.  The open content is the converse — that a rate-free *presentation* of a
completing real can always be re-presented onto a rate-carrying one — which is false in
general (π via Wallis is the obstruction), so C1 sharpens to:

> **C1′.**  The completing reals are *exactly* those with a rate-carrying presentation;
> the rate-free ones (π via Wallis) are completing reals whose *given* presentation is
> not rate-carrying, and the open problem is whether a rate-carrying *re-presentation*
> exists (for π: a fast series — the standing frontier).

This reframes the π frontier as the C1′ existential, not a property of π.

### C2 — the rung floor is the intensional coordinate

The W-relation rungs are now a tower: `W const` (algebraic, `CrossDetConstDenom`, φ) ⊂
`W = d` (`CrossDetEqDenom`, e/Liouville) ⊂ `CrossDetSmall` (free), with the geometric
threshold `r < q` (`GeometricThreshold`) as the sharp boundary, and rescaling moving a
presentation *up* the rungs (`W ↦ c²·W`).  Conjecture:

> **C2.**  Every completing real has a **rung floor** — the lowest W-relation rung
> attained by any of its presentations — and (by `crossDetSmall_rescale_antitone`) it is
> attained at the gcd-reduced presentation.  The rung floor is a rescaling-invariant
> coordinate of the real: φ floors at `W const`, e/Liouville at `W = d`.

This is the original proposal's "내부 좌표차가 역전되는 경계 층" made into an invariant of
the cut, not the presentation — the intensional coordinate the proposal asked for.

### C3 — the analytic and logical invariants are both "the reduced/canonical witness"

`DepthOverflowDuality` already gives the logical side a canonical minimal witness: the
diagonal *is* the least overflow (`diag_is_minOverflow`, `minOverflow_unique`).  The
analytic side now has its canonical witness too: the gcd-reduced presentation
(`crossDetSmall_rescale_antitone`).  Conjecture:

> **C3.**  The intensional content on both sides is "the canonical (minimal/reduced)
> witness": the diagonal `bound + 1` (logical, the unit-surplus floor) and the
> gcd-reduced presentation (analytic, the rung floor).  The presentation-relative junk —
> a larger overflow surplus, a rescaled `c²·W` — is the same redundancy read on the two
> sides, and the unit `1` / the reduced form is the residue in both.

## C2 — first step closed (the rescaling orbit)

`Real213/Spiral/ScalingOrbit` (7 PURE) gives C2 its first ∅-axiom backing, scoped to the
**rescaling** sub-family of presentations.  The presentations `(c·a, c·d)`, `c ≥ 1`, of
one cut form a monoid-action orbit (`scaleBy_one`, `scaleBy_comp`); the cut is the
complete orbit invariant (`scaleBy_preserves_cut`); `CrossDetSmall` is antitone along the
action (`orbit_free_implies_base_free` — the base is the canonical free-witness); and the
orbit has a unique `Reduced` base (`reduced_scaling_trivial`).  So within a rescaling
orbit the **rung floor is attained at the reduced base**, a rescaling-invariant
coordinate.  `scaling_orbit_structure` bundles it.

Scope, honest: this is the rescaling sub-family (common constant factor), not *all*
presentations of a cut.  The rung floor over all presentations — continued-fraction vs
series vs … — is the strictly larger open question (it subsumes C1′).

## Status of the directions

C1′ is the sharpest *new* ∅-axiom target with a concrete obstruction (the converse: when
does a rate-carrying re-presentation exist?).  C2's rescaling-orbit core is now closed
(`ScalingOrbit`); the remaining C2 step is the rung floor over *all* presentations (needs
a cross-presentation invariant, harder).  C3 is a synthesis statement that would bundle
`DepthOverflowDuality` and `IntensionalCompletability`/`ScalingOrbit` (the canonical
witness: diagonal `bound+1` ↔ reduced base).  None imports a classical measure; all live
inside the presentation/cut split that `PresentationDependence` opened.
