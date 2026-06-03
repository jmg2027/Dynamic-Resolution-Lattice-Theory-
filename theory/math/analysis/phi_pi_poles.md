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

## The discriminant is the holonomicity-hierarchy dial

The same `Δ = tr² − 4·det` that splits the φ and π faces is the *order-2 reading* of the whole
holonomicity hierarchy.  Read the recurrence `s(n+2) = p·s(n+1) − q·s(n)` through its **companion
matrix** `comp p q = [[p,−q],[1,0]]`: `EllipticPeriodicTier.comp_disc` gives
`disc (comp p q) = p² − 4q`, *the same discriminant*, and its sign places the recurrence on a
definite rung of the ladder `finite-depth ⊆ C-finite ⊆ P-recursive ⊊ non-holonomic` (the
inclusions themselves ∅-axiom: `CFiniteHomogRec.{order2,order3}_homogRec` put a constant-coefficient
recurrence inside `HomogRec`).  All three rungs are proven, not merely classified:

  - **Elliptic** (`Δ < 0`, unimodular `q = 1`): the companion is a finite-order rotation generator —
    `comp 0 1 = S` (order 4) and `comp 1 1 = U` (order 6), *literally* the elliptic generators of
    the discriminant split (`comp_eq_S`, `comp_eq_U`).  The orbit is **periodic**
    (`periodic_elliptic_S`: `s(n+2)=−s(n)` ⟹ `s(n+4)=s(n)`; `periodic_elliptic_U`:
    `s(n+2)=s(n+1)−s(n)` ⟹ `s(n+6)=s(n)`), the bottom tier — still holonomic
    (`elliptic_S_homogRec`).  This is the π (rotation) face read as a recurrence: bounded, periodic,
    the floor of the ladder.
  - **Parabolic** (`Δ = 0`, `comp 2 1`): the recurrence is `s(n+2) = 2·s(n+1) − s(n)`, i.e.
    `Δ²s = 0` — exactly the degree-`≤1` (linear) polynomials, and this is an **iff**
    (`parabolic_iff_depth1`: the relation holds for all `n` iff `polyDepthZ 1 s`).  The boundary
    discriminant is the depth-1 floor of the generating ring (which *is* the polynomials, by
    `DepthCharacterization.finite_depthZ_iff`).
  - **Hyperbolic** (`Δ > 0`, e.g. `comp 3 1`, the golden/Lucas `Δ = 5`): a real quadratic-irrational
    iterator whose orbit **grows strictly** — `hyperbolic_strictMono` (`s(n+2)=3·s(n+1)−s(n)` with
    `0 < s 0 < s 1` is strictly increasing everywhere, via the invariant
    `s(n+2)−s(n+1) = 2·s(n+1)−s(n) > 0`) and `hyperbolic_grows` (`s 0 + i ≤ s i`, hence unbounded).
    This is the φ (scaling) face read as a recurrence: unbounded partial quotients, the
    quadratic-irrational CF tier.

So the residue's single trace dial reads off the entire ladder: **periodic floor below zero,
linear-polynomial floor at zero, strictly-growing C-finite above zero**.  The φ/π pole structure of
this chapter and the divergence-depth / non-holonomicity hierarchy
(`divergence_depth_characterization.md`, `non_holonomicity_as_finite_state_escape.md`) are not two
subjects but one, seen at the order-2 rung.  Above this rung the dial loses resolution — higher-order
recurrences need the full Casoratian (the discrete Wronskian, `SecondCasoratian`) as order detector,
and the genuine non-holonomic reals (π's continued fraction) have *no* finite Casoratian closure at
all.  φ is the hyperbolic extreme of this ladder (the slowest, all-`1` partial quotients); π is the
pole where no finite order closes.

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
           E213.Lib.Math.Cauchy.PositiveFloorUnbounded \
           E213.Lib.Math.Cauchy.EllipticPeriodicTier \
           E213.Lib.Math.Cauchy.CFiniteHomogRec
cd ..
for m in Real213.HyperbolicEllipticTrace Real213.PentagonGoldenTrace \
         Cauchy.NonHolonomicWitness Cauchy.PositiveFloorUnbounded \
         Cauchy.EllipticPeriodicTier Cauchy.CFiniteHomogRec; do
  python3 tools/scan_axioms.py E213.Lib.Math.$m
done
```
Reports all PURE (`EllipticPeriodicTier` 13, `CFiniteHomogRec` 3).
