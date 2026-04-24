# 20 — Lens as bridge-search infrastructure (2026-04-24)

## The thesis

Raw + Lens is not just a foundational cleanup.  It is a
**quantitative infrastructure for bridge-search in pure
mathematics** — the activity historically performed by
intuition and genius (Langlands, Wiles/Frey/Ribet,
Borcherds, Monstrous Moonshine, Montgomery–Dyson, …).

A "bridge" in mathematics is a non-obvious equivalence,
correspondence, or reduction between two apparently
disjoint domains.  Historically they take decades to
identify and centuries to verify.  Raw + Lens reframes
bridges as **lattice operations on a Lens catalogue**:

> **A bridge between mathematical domains D₁ and D₂ is a
> common Lens L₁₂ such that both D₁'s canonical Lens L₁
> and D₂'s canonical Lens L₂ refine L₁₂** — i.e. L₁₂ is
> a meet in the Lens refinement order.

## Why this is plausible

The 213 Lens catalogue already has the seeds:

1. **R1–R5 profile vector.**  Each Lens is indexed by
   which of R1–R5 it satisfies.  This is a 5-bit
   classifier.  Two Lenses with identical profiles
   are candidates for bridging; differing profiles
   diagnose the obstruction.
2. **Structural axes (comm / assoc / alt / flex).**
   The CD tower (`CDTower.lean`) demonstrates a full
   ✓/✗ matrix.  This extends the classifier with
   algebraic-law survival bits.
3. **`Lens.refines`** is a partial order on Lenses
   (`Hypervisor/Lens.lean`).  Meet / join in this order,
   if completed, provide the bridge-lattice structure
   formally.
4. **`hurwitz_ring` tactic** already automates
   identity-by-identity comparison across layers: given
   a polynomial identity, it decides which CD layer the
   identity survives through.  This is a prototype of
   "quantitative bridge locator".

## Historical bridges, reframed

- **Fermat → Wiles.**  Bridge: Galois-representation
  Lens ∩ automorphic-form Lens, factoring through
  modular-curve geometry.  350-year search ≈
  identification of this meet.
- **Langlands programme.**  Sought meet: shared profile
  between Galois-rep Lens and automorphic Lens on L-
  function space.
- **Monstrous Moonshine.**  Finite-group Lens ∩
  modular-form Lens; common refinement through vertex
  operator algebras (another Lens, retroactively).
- **Montgomery–Dyson on ζ.**  The chance observation
  = two unrelated Lenses (Hilbert-Polya / random-matrix
  / ζ-zero) shared a spectral profile.

## What the infrastructure needs

This note does not claim the infrastructure exists.  It
claims the *components* for it exist in 213:

| Component                     | Status        |
|-------------------------------|---------------|
| R-profile classifier          | partial (R1–R5 + CD axes) |
| Lens refinement partial order | defined (`Lens.refines`) |
| Meet / join algorithms        | not yet |
| Profile-distance metric       | not yet |
| Catalogue of real-math Lenses | ~15 toy Lenses |
| Profile-matching search       | not yet |

**What one session can produce**: formalise profile
vectors for the existing Lens catalogue, define a Hamming
distance on profiles, output a pairwise distance table.
That is the prototype of the bridge-search tool.

## Why this is worth pursuing

Sessions on pure-math research currently diverge into
speculative directions because "where is the bridge"
is unanswerable locally.  A Lens-profile search tool
would narrow candidate bridges from "everywhere" to "in
this 4-dimensional region of the Lens lattice".  Even
partial reduction is useful.

## Downgrade if needed

This is **B-grade** in the overall session arc — not a
trap to avoid, not an orientation fix, but a research
direction.  If the infrastructure is never built, nothing
else in 213 breaks; we just don't benefit from the speedup.

## Relationship to other notes

- `notes/17_existence_mode_lens.md`: bridge-search is
  orthogonal to existence-mode discussions.
- `notes/18_complete_graph_lens_base.md`: K_n is a
  natural common substrate.  Graph-theoretic distance
  between K_n sub-folds = candidate Hamming metric.
- `notes/19_lens_not_functor.md`: the bridge is a Lens,
  not a functor, even when both endpoints are categorical.

## Status

Prose only.  No Lean, no infrastructure yet.  Recorded
here to prevent the "is any of this useful?" loop from
recurring in future sessions — the answer is "yes,
and here's the research programme".
