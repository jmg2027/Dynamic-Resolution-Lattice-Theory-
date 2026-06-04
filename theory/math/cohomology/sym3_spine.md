# Sym(3) spine (cross-frame 8-fold decomposition)

**Status**: Synthesis chapter; all four readings closed elsewhere
(231 PURE across the cited sub-trees).  No new Lean — the chapter
collects four convergent algebraic operations on
K_{3,2}^{(c=2)} and exhibits their shared Sym(3) irrep structure.

## Overview

A single representation of the symmetric group on three letters,

  `8 = 2·trivial ⊕ 3·standard`,

acts as the load-bearing irrep across four otherwise-distant
chapters of the corpus.  The four are not parallel coincidences on
the number 8; they are four count-Lens readings of the same Sym(3)
action on the same K_{3,2}^{(c=2)} cohomological substrate.

The recurrence is recorded as a single citable Lean theorem,
`X1_sym3_cross_frame_capstone`, which conjoins one PURE clause from
each of the four sources.  This chapter is the narrative companion.

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

## Four readings

### Reading 1 — K_{3,2}^{(c=2)} higher cohomology

Chapter: `theory/math/cohomology/k32_higher_cohomology.md`.
The H¹ rank `8 = NS² − 1 = E − V + 1 = χ_rel` is established
directly from cellular cohomology of the bipartite multigraph.  The
2·trivial ⊕ 3·standard split is the Sym(3) irrep decomposition of
that 8-dim F₂ vector space.  ω is the unique Sym(3)-fixed
non-trivial element of H²; the chapter records this as the H²
extension of the spine to `3·trivial ⊕ 3·standard`.

### Reading 2 — 8 Thurston geometries

Chapter: `theory/math/geometry/geometrization_conjecture.md`, step 24.
The 8 Thurston model geometries decompose under the same Sym(3)
action as

  `8 = 3 isotropic + 5 anisotropic`
     `= (2·trivial + 1) + (2·3·standard − 1)`
     `= 3 + 5`,

with the +1 / −1 reshape arithmetic explicit in
`sym3_basis_thurston_mapping`.  The two trivial-irrep generators
`ω_10`, `ω_01` plus the zero translation supply the 3 isotropic
geometries S³, E³, H³; the three standard-irrep basis vectors,
paired into 6 mode-DoF with one overlap collapse, supply the 5
anisotropic geometries S²×ℝ, H²×ℝ, ~SL₂(ℝ), Sol, Nil.

### Reading 3 — Gluon octet (1/α_3)

Chapter: `theory/physics/alpha_em/precision_derivation.md` §5.
The Sym(3) ↪ SU(NS) embedding identifies the 8-dim H¹ basis with
the gluon octet of the strong-coupling adjoint representation:

  `1/α_3 = dim H¹(K) = NS² − 1 = 8 = dim adj SU(3)`.

The F₂-irrep decomposition `2·trivial ⊕ 3·standard` is the same
8-fold structure underlying the gluon count — not a numerical
coincidence on 8 but the *same* Sym(3) action read through the
gauge-content Lens.  Lean anchor: `c3_chain_master`.

### Reading 4 — Akbulut cork twist

Chapter: `theory/math/geometry/exotic_4mfd_cork.md`.  The Z/2 cork-twist
involution on `Cork213` matches the M_S01 transposition acting on
the 8-dim H¹ basis.  The signed orbit count
`signedCorkTwistCount = +4 = 32 − 28` is exactly the difference of
M_S01 fix-counts across twist-even / twist-odd orbits of the
60-element `Sym(3) × Cork213-configurations` space.  Same Sym(3),
same 8-dim H¹ basis, read through the exotic-structure Lens.

## Lean capstone

`lean/E213/Lib/Math/Geometry/GeometrizationConjecture/CrossFrame.lean`
records the 4-way convergence as one citable theorem:

```
theorem X1_sym3_cross_frame_capstone :
    -- Reading 2: Geometrization 8 = 3 iso + 5 aniso
    isotropic_geometry_count = 3
    ∧ anisotropic_geometry_count = 5
    ∧ isotropic_geometry_count + anisotropic_geometry_count = 8
    -- Reading 3: Gluon octet H¹(K) rank, Sym(3) fixedSize
    ∧ H1K.rank = 8
    ∧ Sym3IrrepDecomp.fixedSize = 4
    ∧ 2 + 2 * 3 = 8
    -- Reading 1 (Hodge closure on the same H¹)
    ∧ HC_K32
    -- Möbius P mod-5 pentagonal closure (c=2 forcing)
    ∧ half_period = 5 ∧ full_period = 10 ∧ c_multiplicity = 2
```

The capstone is PURE; each conjunct discharges to a PURE source
elsewhere in the tree.  Reading 4 (cork twist) is connected via the
M_S01 anchor in `AkbulutCork/SignedOrbits.lean` and is registered
in the chapter cross-references rather than as an X-1 conjunct.

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
forced.  The four chapter readings each Lens-restrict to a
different observable (geometry classification, gauge count, Hodge
closure, exotic-structure invariant), but they are restrictions of
one structural object.

## Open frontier

- **Extension to ω-weighted H²**: the spine extends from
  `2·trivial ⊕ 3·standard` (H¹) to `3·trivial ⊕ 3·standard`
  (H¹ + H², adding the ω invariant).  Whether the four Lens
  readings each extend to the H² level is partially answered
  (Reading 1 yes via the k32 chapter; Reading 3 yes via the α_em
  0.007 ppb tier; Readings 2 and 4 open).
- **Higher-cohomology cork-twist** is the Reading 4 sub-question
  for H² / H³ — explicitly tracked in
  `theory/math/geometry/exotic_4mfd_cork.md` Open Frontier.

## Connection

- `theory/math/cohomology/k32_higher_cohomology.md` — Reading 1
- `theory/math/geometry/geometrization_conjecture.md` — Reading 2 + the
  X-1 capstone home chapter
- `theory/physics/alpha_em/precision_derivation.md` — Reading 3
- `theory/math/geometry/exotic_4mfd_cork.md` — Reading 4
- `theory/math/geometry/generation_rule.md` — why (NS, NT) = (3, 2) is
  forced; the structural origin of Sym(3)
- `theory/meta/methodology_patterns.md` — Pattern of cross-frame
  count-Lens convergence on a shared algebraic object
