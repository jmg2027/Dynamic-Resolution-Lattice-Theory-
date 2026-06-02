# The φ and π poles — hyperbolic and elliptic faces, and why holonomicity is a property of the pointing

**Status**: theorem-anchored synthesis; the headline open frontier (π's continued-fraction
non-holonomicity) is stated as the boundary, not claimed.  Every assertion below is backed by a
∅-axiom theorem named inline.

## Overview

Two reals organise the continued-fraction approximation spectrum at its extremes.  The golden
ratio φ is the **floor**: its partial quotients are all `1` (`QuasiPolyCF 1`,
`LagrangeExtremes`), the slowest possible, and its Lagrange value `√5` is the spectrum minimum
(`GoldenFormMarkov`).  π is the **pole**: its partial quotients are unbounded and its
continued fraction is conjectured non-holonomic — the regularity opposite of φ.  This chapter
assembles the proven structure around the two poles: they are the **hyperbolic** and
**elliptic** faces of one `SL(2, ℤ)` story, φ lives on the crystallographically *forbidden*
axis, and — the load-bearing point — *holonomicity is a property of the pointing, not of the
real*, which is exactly why π can be non-holonomic in one presentation and finite-depth in
another with no contradiction and no exterior.

## The discriminant sign — hyperbolic φ, elliptic π

A determinant-one `2×2` integer matrix is classified by its discriminant `Δ = tr² − 4·det =
tr² − 4` (`HyperbolicEllipticTrace`):

  - **Hyperbolic** (`Δ > 0`): real eigenvalues `(tr ± √Δ)/2`, a scaling.  The golden iterator
    `G = [[2,1],[1,1]]` has `det = 1`, `tr = 3`, `Δ = 5` (`golden_hyperbolic`); its eigenvalues
    are `φ²` and `φ⁻²`, and it is the residue's self-reference iterator — the Möbius map
    `P(x) = (2x+1)/(x+1)` whose fixed point is φ (`Mobius213`).  The trace `3` is `NS`, the
    discriminant `5` is `NS + NT`.
  - **Elliptic** (`Δ < 0`): complex eigenvalues on the unit circle, a rotation.  `S =
    [[0,−1],[1,0]]` has `tr = 0`, `Δ = −4`, `S² = −I`, `S⁴ = I` (`S_elliptic_order4`); `U =
    [[1,−1],[1,0]]` has `tr = 1`, `Δ = −3`, `U³ = −I`, `U⁶ = I` (`U_elliptic_order6`).  These
    are the elliptic generators of `PSL(2, ℤ) = ℤ₂ * ℤ₃` (`ModularElliptic`), orders `4` and
    `6`.

The sign of `Δ` is the φ/π split (`wick_discriminant_split`: `0 < disc G ∧ disc S < 0 ∧ disc U
< 0`).  The hyperbolic trace is `2cosh t` (`> 2`), the elliptic trace is `2cos θ` (`∈ (−2,2)`);
the identity `cos(iθ) = cosh θ` is the single continuous bridge between the faces, and the
substitution `θ ↦ iθ` is exactly the flip of `Δ`'s sign.  φ is the scaling (hyperbolic) face,
π the rotation (elliptic) face, of one continuous structure.

## The golden ratio sits on the forbidden axis

The crystallographic restriction allows rotation orders `{1,2,3,4,6}` only
(`Tower/CyclotomicTraceDegree.crystallographic_restriction`); their traces `2cos(2πk/6)` are
the integers `{2,1,−1,−2}` (`ImaginaryQuadraticUnitTrichotomy.crystallographic_cosines`).  The
forbidden orders `5` and `10` are precisely where the *golden* trace appears
(`PentagonGoldenTrace`):

  - `2cos(2π/5) = φ − 1`, the root of `x² + x − 1` (`pentagon_trace_quad`), equal to `1/φ`
    (`pentagon_trace_unit`: `φ·(φ−1) = 1`);
  - `2cos(π/5) = φ`, the root of `x² − x − 1` (`phi_quad`: `φ² = φ + 1`).

Both are golden integers of `ℤ[φ]`, not rational integers — the algebraic skeleton of `φ =
2cos(π/5)`.  φ and `1/φ` are the norm-`−1` units of `ℤ[φ]` (`phi_norm`, `pentagon_trace_norm`),
whose power-ladder carries the alternating Cassini determinant `(−1)ⁿ` (`FibCassiniNat`).  So
the golden ratio is what the rotational-trace reading returns on the axis the crystallographic
orders cannot occupy.

## Holonomicity is a property of the pointing, not of the real

The continued-fraction holonomicity tiers (`cf_holonomicity_hierarchy.md`) climb from periodic
(quadratic irrationals) through Hurwitzian (e, tan 1) to non-Hurwitzian (`2ⁿ`, still C-finite)
to genuinely non-holonomic, the last inhabited ∅-axiom by `(n!)ⁿ`
(`NonHolonomicWitness.superFact_nonHolonomic`).  It is tempting to read "π is non-holonomic" as
a property of the number π.  It is not.  Holonomicity is read off an **approximant sequence** —
a pointing — and the same real admits pointings of different recurrence structure.

This is a theorem.  `PresentationDependence.crossDetSmall_is_presentation_dependent` exhibits a
real whose cross-determinant (the holonomic-bridge quantity) is small in one presentation and
not in another `×c` rescaling of the *same* real, while `rcut_rescale` proves the underlying
cut is invariant under `(a, d) ↦ (c·a, c·d)`.  The recurrence structure belongs to the
representation; the real does not change.

For π the two pointings are explicit:

  - the **regular continued fraction** pointing: its partial-quotient sequence is conjectured
    to satisfy no finite recurrence (non-holonomic), the pole tier of
    `cf_holonomicity_hierarchy.md`;
  - the **Wallis** pointing: its convergent-ratio sequence has a finite difference depth —
    `DepthPiQuartic.liftK4_piRatio` shows the fourth finite difference of π's Wallis ratio is
    the constant `384`, so the *rationals* of this pointing are holonomic.

These do not contradict, and no exterior distinguishes them: both are residue-internal
pointings, and divergence depth is presentation-relative.  Crucially, **neither pointing
reaches π** — both only converge.  Every real's convergents carry the unit cross-determinant
`W² = 1` (`ContinuedFractionFloor.cf_det_sq`), so a real is bracketed by its convergents but is
outside their image (`FlatOntologyClosure.object1_not_surjective`): π is the limit of each
pointing and equal to no term of either.  The finite det-1 structure of the Wallis rationals
is a feature of that pointing, not a capture of π; the absence of a finite structure in the
continued-fraction pointing is a feature of that pointing, not an intrinsic mark on π.  π is
neither holonomic nor non-holonomic — those predicates classify pointings, and π is the
invariant residue every pointing approximates.

This is the Archimedean reading made precise: π is bracketed between inscribed (lower) and
circumscribed (upper) regular-polygon perimeters — the cross-determinant `±1` squeeze seeded
from the allowed axes `4` (square) and `6` (hexagon) that bracket the forbidden `5`.  The
squeeze is a pointing; it converges to π and equals no bound.

## The open frontier

That π's *regular continued fraction* is non-holonomic is classically open and not closable
∅-axiom.  The provable neighbours are closed: the genuine non-holonomic tier is inhabited
(`NonHolonomicWitness`), a positive constant top finite-difference forces unboundedness
(`PositiveFloorUnbounded.positive_floor_unbounded`, whence e's partial quotients are unbounded,
`ePQ_unbounded`), and the elementary Klazar growth bound is formalised through the holonomic
growth majorant (`NonHolonomicWitness.holonomicGrowth_envelope`).  The growth route does not
reach π — π's partial quotients are not super-factorial — so the residual obstruction is one of
asymptotic *shape* (Flajolet–Gerhold–Salvy), which is analytic and bottoms out, for π, at the
unproven hypothesis that π's partial quotients are Gauss–Kuzmin distributed.  The boundary is
sharp: what the discrete, constructive setting can certify is the hierarchy and its inhabited
genuine tier; what it cannot is the analytic shape obstruction that the specific number π would
require.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Real213.HyperbolicEllipticTrace \
           E213.Lib.Math.Real213.PentagonGoldenTrace \
           E213.Lib.Math.Cauchy.NonHolonomicWitness \
           E213.Lib.Math.Cauchy.PositiveFloorUnbounded
cd ..
for m in Real213.HyperbolicEllipticTrace Real213.PentagonGoldenTrace \
         Cauchy.NonHolonomicWitness Cauchy.PositiveFloorUnbounded; do
  python3 tools/scan_axioms.py E213.Lib.Math.$m
done
```
Reports all PURE.
