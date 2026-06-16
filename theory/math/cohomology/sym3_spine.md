# Sym(3) spine (cross-frame 8-fold decomposition)

**Status**: Synthesis chapter; both readings closed elsewhere
(PURE across the cited sub-trees).  No new Lean — the chapter
collects two convergent algebraic operations on
K_{3,2}^{(c=2)} and exhibits their shared Sym(3) irrep structure.

## Overview

A single representation of the symmetric group on three letters,

  `8 = 2·trivial ⊕ 3·standard`,

acts as the load-bearing irrep across two otherwise-distant
chapters of the corpus.  The two are not parallel coincidences on
the number 8; they are two count-Lens readings of the same Sym(3)
action on the same K_{3,2}^{(c=2)} cohomological substrate.

The shared decomposition is anchored by `Sym3IrrepDecomp.fixedSize_eq_4`
and the gauge reading `c3_chain_master` (both PURE).  This chapter is
the narrative companion.

## The shared decomposition

`H¹(K_{3,2}^{(c=2)})` carries a natural Sym(3) action permuting the
three S-vertices.  Three explicit involutions generate it:

- `M_S01` — swap S-vertices 0 ↔ 1 (Face 2 fixed)
- `M_S12` — swap S-vertices 1 ↔ 2 (Face 0 fixed)
- `M_S02` — swap S-vertices 0 ↔ 2 (Face 1 fixed)

As an 8-dimensional F₂ representation of Sym(3), the irrep
decomposition is

  `dim H¹ = 8 = 2·trivial ⊕ 3·standard`,

with `fixedSize = 4` (the dim-2 trivial subspace plus its zero
vector, plus the three rank-zero standard-irrep diagonals).  The
unique non-trivial Sym(3)-invariant 2-cocycle at H² is `ω = (1,1,1)`
(`phase2_omega_invariant_2cocycle`), extending the H¹+H² spectrum
to `3·trivial ⊕ 3·standard`.

## Two readings

### Reading 1 — K_{3,2}^{(c=2)} higher cohomology

Chapter: `theory/math/cohomology/k32_higher_cohomology.md`.
The H¹ rank `8 = NS² − 1 = E − V + 1 = χ_rel` is established
directly from cellular cohomology of the bipartite multigraph.  The
2·trivial ⊕ 3·standard split is the Sym(3) irrep decomposition of
that 8-dim F₂ vector space.  ω is the unique Sym(3)-fixed
non-trivial element of H²; the chapter records this as the H²
extension of the spine to `3·trivial ⊕ 3·standard`.

### Reading 2 — Gluon octet (1/α_3)

Chapter: `theory/physics/alpha_em/precision_derivation.md` §5.
The Sym(3) ↪ SU(NS) embedding identifies the 8-dim H¹ basis with
the gluon octet of the strong-coupling adjoint representation:

  `1/α_3 = dim H¹(K) = NS² − 1 = 8 = dim adj SU(3)`.

The F₂-irrep decomposition `2·trivial ⊕ 3·standard` is the same
8-fold structure underlying the gluon count — not a numerical
coincidence on 8 but the *same* Sym(3) action read through the
gauge-content Lens.  Lean anchor: `c3_chain_master`.

## Lean anchors

The two readings share one PURE Sym(3) substrate:

- `Sym3IrrepDecomp.fixedSize_eq_4` — the dim-2 trivial-isotypic
  subspace (4 fixed cochains) of H¹(K_{3,2}^{(c=2)}) over F₂.
- `c3_chain_master` — the gluon-octet reading `1/α_3 = dim H¹ =
  NS² − 1 = 8 = dim adj SU(3)`.

Both discharge to PURE sources; the chapter records their shared
Sym(3) action as narrative rather than as a single conjoined theorem.

## Why Sym(3) at d = 5

The structural origin is the generation rule.  Starting from the
distinguishing primitive, the first orthogonal-direction count
forces `NT = 2`; the second orthogonal-direction count, refusing
self-pairing (Clause 4), forces `NS = 3`
(`theory/math/geometry/generation_rule.md`).  The Sym(3) symmetry is the
automorphism group of those 3 forced orthogonal directions — it is
not chosen, it is the action that exists on a 3-element forced set.

The chartBase coincidence `d = NS + NT = 5` is where the forced
triplet crystallises as the K_{3,2}^{(c=2)} substrate.  The
8 = NS² − 1 dimension of H¹ is the F₂-vector space on which Sym(3)
naturally lifts as a 4-dim trivial + 6-dim standard partition,
recombined as `2·trivial ⊕ 3·standard` once the cohomological
boundary identifications are applied.

Sym(3) is therefore not imposed on K_{3,2}^{(c=2)} from outside —
it is the symmetry that has to be there once `(NS, NT) = (3, 2)` is
forced.  The two chapter readings each Lens-restrict to a
different observable (cohomology closure, gauge count), but they are
restrictions of one structural object.

## Open frontier

- **Extension to ω-weighted H²**: the spine extends from
  `2·trivial ⊕ 3·standard` (H¹) to `3·trivial ⊕ 3·standard`
  (H¹ + H², adding the ω invariant).  Whether both Lens
  readings extend to the H² level is partially answered
  (Reading 1 yes via the k32 chapter; Reading 2 yes via the α_em
  0.007 ppb tier).

## Connection

- `theory/math/cohomology/k32_higher_cohomology.md` — Reading 1
- `theory/physics/alpha_em/precision_derivation.md` — Reading 2
- `theory/math/geometry/generation_rule.md` — why (NS, NT) = (3, 2) is
  forced; the structural origin of Sym(3)
- `theory/meta/methodology_patterns.md` — Pattern of cross-frame
  count-Lens convergence on a shared algebraic object
