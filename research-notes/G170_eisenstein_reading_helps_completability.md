# G170 — does the Eisenstein/elliptic conjecture help the completability candidates?

**Date**: 2026-06-01.  **Status**: synthesis + supporting ∅-axiom lemmas.
**Source of truth**: `lean/E213/Lib/Math/Real213/CrossDetDiscriminant.lean` (3 PURE).
**Anchors**: the Eisenstein conjecture note (`G167_crossdet_number_field_eisenstein_conjecture`,
the other branch), `Real213/{ProbeTwistConic, IntensionalCompletability, ScalingOrbit,
CrossDetEqDenom, CrossDetConstDenom}`, `Cauchy/{DepthFloorDetOne, DepthOverflowDuality}`,
the C1′/C2/C3 conjectures (`G169`).

## The question

The other branch is developing the **Eisenstein/elliptic** reading of the
cross-determinant `(W, d)` plane: alongside the `W = ±1` (det-one) and `W = d`
references, an *Eisenstein* reference appears — and, because `ℤ[ω]` is imaginary-quadratic,
it is a **curve (torus / `j=0` elliptic-curve lattice)**, not a *line*.  The
line-vs-curve shape is forced by the **sign of the discriminant**: golden `m²−mk−k²`
(disc `+5`) is indefinite (unbounded → line); Eisenstein `a²−ab+b²` (disc `−3`) is
definite (bounded → curve).  Does this help the completability candidates C1′/C2/C3?

## Answer: it gives C2 an algebraic backbone, and ties C3 to the residue; orthogonal to C1′/π

**C2 (the rung floor) — yes, directly.**  C2 asked for the rung floor to be a
rescaling-invariant *coordinate* of the cut.  The Eisenstein reading supplies what the
coordinate *is, algebraically*: the cross-determinant's quadratic reference, classified by
discriminant.  Concretely, the bottom of the rate-carrying stratification is the **det-one
floor** (`W ≡ 1`, `DepthFloorDetOne`; my `floor_carries_Htel`, the trivially-free bottom of
`RateStratification`), and that floor's conserved invariant is the **golden form** `Q =
m²−mk−k²` (`ProbeTwistConic.Q_preserved`).  The Eisenstein note's claim is that this golden
floor is the *real-quadratic, disc `+5`, indefinite* rung — and that is exactly why it
**completes via a convergent line** (the infinite `ℤ[φ]` unit group `φⁿ` = the P-orbit, the
closed-form modulus `N = 2k`).  So C2's rung floor acquires an algebraic character:

> **C2 (refined).**  The rung floor is the *discriminant / quadratic order* of the reduced
> presentation's cross-determinant.  The det-one floor is the indefinite (disc `+5`)
> rung — a convergent line — the completing bottom.

This is now ∅-axiom-backed at its heart (`CrossDetDiscriminant`, below).

**C3 (the canonical witness = residue) — yes, conceptually.**  The Eisenstein note's
deepest reading is that the divergent/overtake trajectory is the **residue**, the
Eisenstein lift is a finer Lens, and modularity is a **self-covering symmetry** — *the same
self-covering as `DepthCeilingResidue`*, now at the scale of the modular surface, with the
**cusp the residue** (the tower with no top).  That is precisely the object
`DepthOverflowDuality` already builds on (`ceiling_residue_is_pointing_residue`).  So C3
(the canonical witness is the residue on both sides) and the Eisenstein "cusp = residue"
are the same statement at two scales — a synthesis target, not yet a theorem.

**C1′ / π — no direct help.**  C1′ (a completing real = one with a rate-carrying
re-presentation) and π are about *rate* and *presentation*, orthogonal to the number-field
structure of `W`.  The discriminant classifies *which algebraic locus* a presentation's
cross-determinant sits in; it does not produce a fast re-presentation.  Honest: the
Eisenstein reading does not move π.

## Closed this step (the ∅-axiom heart, over ℕ)

The Eisenstein conjecture's *signed-`ℤ[ω]`* form (`eisenstein_norm_posdef` over `ℤ`) is
blocked on a pure `Int` polynomial-identity normalizer (the other branch's open
infrastructure item).  But the **dichotomy's heart needs no signed arithmetic** — it is
visible over `ℕ` as a sign comparison `a·b ⋚ a²+b²`, and `CrossDetDiscriminant` proves it:

  - `eisenstein_definite` — `a·b ≤ a²+b²` for all `a, b`: the Eisenstein form `a²−ab+b²`
    is never negative (positive-definite → **bounded** level sets → torus / curve).
    Pure: the larger of `a, b` absorbs the cross term into its square.
  - `golden_indefinite` — the golden form `m²−mk−k²` takes both signs (`+1` at `(1,0)`,
    `−1` at `(1,1)`): indefinite → **unbounded** level sets → convergent line.
  - `discriminant_dichotomy` — bundles them: definite (curve) vs indefinite (line, the
    det-one floor = completing bottom).

So "line vs curve" — the geometric core of Mingu's Eisenstein intuition — is an ∅-axiom
`ℕ` fact about the sign of the discriminant, *independent* of the elliptic-curve / CM /
modular edifice (which stays out of scope) and of the blocked signed-`ℤ` normalizer.

## What this opens (still ∅-axiom-shaped)

  - **C2 refined → a `rung ↔ discriminant` theorem.**  Tie the W-relation rungs (`W const`
    ⊂ `W=d` ⊂ `CrossDetSmall`) to quadratic-order data: the det-one floor is disc `+5`; the
    open step is naming the discriminant of the `W=d` and geometric rungs and proving the
    inclusion is a discriminant ordering.
  - **The pure `Int` poly-identity normalizer** (the other branch's blocker) would unblock
    the *signed* `ℤ[ω]` cross-determinant (`eisenstein_norm_posdef`, target #1 there) and
    is reusable for any signed-cross-determinant extension of the stratification — a
    separable infrastructure task (the `Int` analog of `Meta/Nat/PolyNat.poly_id`).
  - **C3 synthesis** — bundle `DepthOverflowDuality` (cusp/diagonal = residue) with the
    Eisenstein modular self-covering once the lattice-Lens has a 213-native statement.

One line: the Eisenstein reading does not give a new *rate* (so π/C1′ are untouched), but
it gives the **rung floor (C2) its algebraic identity — the discriminant of the
cross-determinant's quadratic reference — and ties the residue (C3) to the modular
self-covering**, with the line-vs-curve heart now ∅-axiom over ℕ.
