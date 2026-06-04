# G170 — does the Eisenstein/elliptic conjecture help the completability candidates?

**Date**: 2026-06-01.  **Status**: synthesis; the dichotomy is closed ∅-axiom.
**Source of truth**: `lean/E213/Lib/Math/CayleyDickson/Integer/EisensteinSignature.lean`
(the signed-ℤ dichotomy, via the bivariate `Int` reflection prover `Meta/Int213/PolyInt2`).
**Anchors**: the Eisenstein conjecture note (`G167_crossdet_number_field_eisenstein_conjecture`),
`Real213/{ProbeTwistConic, IntensionalCompletability, ScalingOrbit, CrossDetEqDenom,
CrossDetConstDenom}`, `Cauchy/{DepthFloorDetOne, DepthOverflowDuality}`, the C1′/C2/C3
conjectures (`G169`).

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

This is now ∅-axiom-backed at its heart (`EisensteinSignature`, below), and the
completability-side (line) half is `Real213/FloorReferenceForm.floor_reference_is_indefinite`:
the det-one floor preserves the golden form (`Q_preserved`) and that form is indefinite
(`golden_indefinite`, `Q(2,1)=+1`, `Q(1,1)=−1`) — the disc+5 / convergent-line / completing
bottom rung, in-track (no CD import).

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

## Closed (the dichotomy, over signed ℤ)

The dichotomy is closed ∅-axiom in `CayleyDickson/Integer/EisensteinSignature`, on the
genuine signed forms, via the bivariate `Int` reflection prover `Meta/Int213/PolyInt2`
(the `Int` analog of `PolyNat`, the infrastructure item G170 first flagged — now built):

  - `eisForm_nonneg` — `0 ≤ a²−ab+b²` for all `a, b : Int`, through `2·N = a² + b² +
    (a−b)²` (`two_eisForm`, by `poly_id2`) and sum-of-squares nonneg.  `eisenstein_norm_nonneg`
    is the same for `ZOmega.normSq` — the Eisenstein form is positive-**definite** ⟹
    **bounded** level sets ⟹ torus / `j=0` elliptic-curve lattice.
  - `golden_indefinite` — `goldenForm 1 0 = 1`, `goldenForm 1 1 = −1`: the disc `+5`
    golden form takes both signs ⟹ **unbounded** level sets ⟹ convergent line.
  - `signature_dichotomy` — definite (curve) vs indefinite (line, the det-one floor =
    completing bottom).

So "line vs curve" — the geometric core of Mingu's Eisenstein intuition — is an ∅-axiom
fact about the sign of the discriminant, on the real `ℤ` forms (tied to `ZOmega.normSq`),
*independent* of the elliptic-curve / CM / modular edifice (which stays out of scope).
(An earlier ℕ-visible sidestep proved `a·b ≤ a²+b²`; it is removed now that the signed-ℤ
`PolyInt2` route exists and is canonical.)

**The trichotomy, completed.**  `CayleyDickson/Integer/ParabolicSignature` adds the
degenerate **disc `0`** middle: `parabForm m k = (m−k)²` is semi-definite (`parab_nonneg`,
a square) with a *non-origin* zero (`parab_nonorigin_zero`, `parabForm 1 1 = 0`, vanishing
on a line) — the **parabolic cusp** between the indefinite golden line (disc `+5`) and the
definite Eisenstein curve (disc `−3`).  `signature_trichotomy` bundles disc `+5` / `0` /
`−3` = line / cusp / curve, mirroring the `SL₂(ℤ)` trace trichotomy (|tr| > 2 / = 2 / < 2).
The cusp is the rational direction — the genuine, irreducible divergence of the geodesic
coding, i.e. the **residue** read at the modular-surface scale (the one cusp of
`ℍ/SL₂(ℤ)`), tying the discriminant trichotomy back to `DepthOverflowDuality`/
`DepthCeilingResidue` (C3).

## What this opens (still ∅-axiom-shaped)

  - **C2 refined → a `rung ↔ discriminant` theorem.**  Tie the W-relation rungs (`W const`
    ⊂ `W=d` ⊂ `CrossDetSmall`) to quadratic-order data: the det-one floor is disc `+5`; the
    open step is naming the discriminant of the `W=d` and geometric rungs and proving the
    inclusion is a discriminant ordering.
  - **The pure `Int` poly-identity normalizer is now built** (`Meta/Int213/PolyInt2`,
    `poly_id2`, bivariate) — the infrastructure item first flagged here — and it carried
    the signed-ℤ `eisForm_nonneg`.  It is reusable for any signed-cross-determinant
    extension of the stratification.
  - **C3 synthesis** — bundle `DepthOverflowDuality` (cusp/diagonal = residue) with the
    Eisenstein modular self-covering once the lattice-Lens has a 213-native statement.

One line: the Eisenstein reading does not give a new *rate* (so π/C1′ are untouched), but
it gives the **rung floor (C2) its algebraic identity — the discriminant of the
cross-determinant's quadratic reference — and ties the residue (C3) to the modular
self-covering**, with the line-vs-curve heart now ∅-axiom over ℕ.
