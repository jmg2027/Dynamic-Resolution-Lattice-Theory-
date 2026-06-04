# The towers of 213 — one matrix, many readings

The framework's "towers" — Cayley-Dickson, universe chain, P-orbit, GRA,
Raw self-iteration, fractal cohomology — are not parallel hierarchies.
They are **one** self-pointing orbit read through different Lenses, whose
single algebraic shadow is the matrix `P = [[2,1],[1,1]]`.

## 213-native answer

There is one tower.  "Going up a level" is the residue pointing at its
own previous pointing once more; the count-Lens reading of "distinguish,
then distinguish again" is exactly the matrix `P = [[2,1],[1,1]]` —
trace `3 = NS`, determinant `1`, the unique `SL(2,ℤ)₊` matrix with that
signature (`Mobius213/Px/CharPolySelf.p_self_reference_master`).  Every
named tower below is this one orbit read by a different Lens, not a
separate object.  The matrix is simultaneously object, theory and
notation (`Mobius213/Px/MobiusSelfForm`; `math/mobius213_p_orbit_closure.md`).

## Derivation — the six readings

**Raw self-iteration** is the orbit before any Lens: `slash` raises depth
by one, the inhabitant count follows `|Sₙ| = 2 + C(|Sₙ₋₁|, 2)`, and every
tree obeys `depth < leaves` (`Theory/Raw/Levels.Raw.depth_lt_leaves`;
`Lib/Math/Foundations/UniverseChain/RawRecurrence.rawCount_recurrence_witness`).  Its
most primitive single thread is named directly — `rawTower n = a/(a/…/b)`,
the one `slash` arrow iterated from the first distinguishing, with
`depth = level` and `depth < leaves` at every rung
(`Theory/Raw/PrimitiveTower.{rawTower, primitive_tower_summary}`, ∅-axiom).
Every named tower below is this spine with `slash` replaced by a chosen
step — a Lens reading sitting above this object.

**The Möbius reading** sends `(p,q) ↦ (2p+q, p+q)`; its convergents
approach φ, bracketed by φ² (`Mobius213/TowerLInfty.tower_growth_phi_squared_bracket`),
and the trajectory is the unique Pell-unit-invariant sequence
(`Mobius213/TowerConvergence.tower_L_infty_exists`).  Its fixed point is
`P(φ) = φ`, φ = (1+√5)/2 (`seed/AXIOM/05_no_exterior.md` §5.6).

**The GRA reading** (Graded Residue Arithmetic) reads the same data as a
depth `⌈n/3⌉` on two coprime generators `(NT,NS) = (2,3)`; its five
domain-Readings (NumberTheory / Graph / Analysis / Cohomology / HoTT /
HigherAlgebra) are pairwise isomorphic through the NT hub
(`GRA/HigherAlgebra.gra_universality_witness`), a property proved for
`⌈n/3⌉` transfers to all five at once
(`GRA/Translation.master_translation_from_any`), and they collapse to a
single `LensIso` class (`GRA/LensIsoCapstone`; `THEORY_BOOK.md` Part VI).

**The universe-chain reading** scales by `numV(L) = 5^L`
(`replicate_image_card : numV 2 = numV 1 · numV 1`); the count at
fractal level 2 is a bounded Lens output, not a universe constant
(`Lib/Math/Foundations/UniverseChain/`).  Its
topological shadow is the Betti spectrum of `K_{5^L}`
(`Cohomology/Fractal/Level.fractal_betti_spectrum`).

**The Cayley-Dickson reading** is the grade/algebra axis: each `CDDouble`
drops one law (commutativity → associativity → alternativity →
composition).  The single inductive mechanism is generic —
`(0,u)² = (−|u|²,0)` at every layer (`Theory/CDDouble/UniversalOrder4.cdd_lift_squared`)
— the `{±1}` subring is preserved at every rung
(`CayleyDickson/Tower/TowerFixedPoint.tower_fixed_point_summary`,
`typeA_non_order4_fixed_at_2`), and the Moufang-failure asymptote
`1 − (1/2)·(1/φ)^rank` is governed by P's eigenvalues.

## The single object, and the constant residue 2

Every reading carries the **same fixed residue, of size 2**: `{±1}` (CD),
the Pell unit `−1` (Möbius), the two atoms `{a,b}` (Raw), the constant
`d = 5` parameter (universe chain).  This is `NT = 2` surviving every
ascent — the count-Lens reading of the first distinguishing
(`seed/AXIOM/05_no_exterior.md`).  P's characteristic polynomial
`x² − 3x + 1` (trace `NS = 3`, det `1`) has eigenvalues φ² and 1/φ²:
*the same* φ that is the CD asymptote, the universe-chain limit, and the
Möbius fixed point.  The bundling is explicit:
`Lib/Math/Mobius213GrandUnification.grand_unification` is a ten-conjunct
theorem naming P across cut-algebra equality, the K_{3,2} signature,
Pell-Fibonacci recurrence, and — conjunct **H** — the **Cayley-Dickson
Type C asymptote `(disc P, Pell unit) = (5, −1)`**.  The CD tower is, to
the letter, one conjunct of the grand unification.

## Dual function

Read classically, the Fibonacci recurrence, the Frobenius coin problem,
the fractal complete graphs, and the Cayley-Dickson algebras are
different objects in different fields.  Stripped of packaging, each is
the same self-pointing orbit under one Lens — number, arithmetic,
topology, algebra.  213's reading is sharper than "these are analogous":
they are the **same Lens-kernel on Raw**, witnessed by the pairwise GRA
isomorphisms and the ten-conjunct `grand_unification`, not asserted by
resemblance.  Where a classical account would prove each tower
separately, here a fact proved for `⌈n/3⌉` *is* the fact for all of them
(`master_translation_from_any`).

## Cross-frame connections

Three frames converge.  **No-exterior** (`05_no_exterior.md` §5.1): no
outside vantage selects which tower is "primary"; they are co-present
readings, so the question "which is the real tower?" has no operand.
**Fixed point** (§5.6): `P(φ) = φ` is the algebraic image of the minimum
residue, and *every* tower's limit is φ or a power of it — the towers
share a limit because they share the orbit.  **Object/theory/notation
non-separation**: P is at once the carrier, the recurrence, and the
matrix that writes them (`MobiusSelfForm`) — the same collapse that makes
"is the tower frozen or dynamic?" (§5.7) malformed.

## Boundary — what is *not* this tower

Not every object the repo names "tower" is this orbit.  Naming three
constructions "tower" by their iteration motif and then reading them as
the same object would be exactly the meaning-by-resemblance the framework
refuses (`05_no_exterior.md` §5.4).  The honest map separates them:

  - **Resolution/cardinality axis** — the Cantor tower of iterated
    function spaces `Raw → (Raw→Bool) → ((Raw→Bool)→Bool) → …`, each rung
    with no surjection from the previous (`Lens/Cardinality/Tower`,
    Σ6), the `Lensⁿ α` image-collapse tower
    (`Lens/Properties/TowerLevel3`), and the hyperreal
    `Hyper/Hyper213Tower` construction.  These ascend by the **Lens
    diagonal**, not by P-iteration; their quantitative shadow is the
    universe-chain `5^L` reading above (which *is* in the orbit).  The
    diagonal and the orbit are distinct constructions that coincide only
    on that shared bounded scale, not as one object.
  - **ℝ-encoding tower** — `TriangularTower/` encodes reals as
    finite-level squashed paths under `NS = 3` absorption
    (`theory/math/geometry/triangular_tower.md`).  It borrows the signature `NS`,
    but it is a *representation* construction, not the doubling-arrow
    orbit.
  - **Physics hierarchy towers** — `Physics/Mass/HierarchyTowers` stacks
    DRLT mass ratios (`m_μ/m_e`, `m_τ/m_μ`) from `(NS,NT)`; these are the
    signature's *observable fingerprint* (DRLT deployment), one layer
    downstream of the 213-math orbit.

A fourth construction makes the boundary explicit in Lean:
`Lib/Math/Geometry/LevelTopology/TwoTowersDivergence` proves the 213 tower
**diverges** from the classical Cayley-Dickson tower — 213 carries sign
as an orthogonal floor where classical CD keeps it internal — so even the
CD reading is the orbit's, not the textbook construction's.

## Open frontier

The GRA-tower ↔ CD-tower *duality* (level `n` of property loss ↔ level
`5−n` of Reading-iso gain) is conceptual only (`math/gra_book.md` §5.3,
Conjecture 5.3.1).  The "every axis sees P" catalog stands at 55 axes
(`theory/essays/every_axis_sees_p.md`); whether it is exhaustive is open.
And within the CD column, the flexibility rung past Cayley is not yet
closed (`Meta/Algebra213/CDDoubleFlexible.lean`; see
`math/cayley_dickson/algebra_tower.md` §"Open frontier" #2 and
`theory/essays/cd_tower_polarization.md`).
