# G167 — the cross-determinant classification's number-field reading, and the Eisenstein/elliptic conjecture

**Date**: 2026-06-01.  **Status**: conjecture (originator: Mingu Jeong) + repo-grounded
analysis.  **Tier**: 1 (research scratch — open frontier, not promoted).

## The seed (Mingu Jeong)

> If the `y = x` (`W = d`) reference is a "dyadic" reference line, then from the 213
> perspective an *Eisenstein* reference should also exist — and it would appear as a
> reference **curve via an elliptic curve**, not a line.

This note tests that against what the repo actually contains and isolates the precise,
∅-axiom-shaped core that survives.

## The (W, d) plane, in number-field terms

The completability classification (`theory/math/analysis/tower_native_completeness.md`)
lives in the plane of `(W_i, d_i)` where `W_i = a_{i+1}d_i − a_i d_{i+1}` is the **2×2
cross-determinant** of consecutive convergent vectors `(a_i, d_i)` — the `SL₂(ℤ)` /
continued-fraction structure.  Two reference lines:

  - **`W = ±1` (the det-one floor)** — unimodular determinants = `SL₂(ℤ)`.  This is the
    **golden / √5** locus: the preserved form is `Q(m,k) = m² − mk − k²`
    (`ProbeTwistConic.Q_preserved`), **discriminant `+5 = NS + NT`**, the ring `ℤ[φ]`,
    `P = [[2,1],[1,1]]` with trace `3 = NS`, det `1 = NS − NT`.  φ, √2, √3 (Pell).
  - **`W = d` (the diagonal)** — the reciprocal-series line `Σ 1/d_j`
    (`ReciprocalSeries`), a `g = d_{i+1}/d_i`-graded family; e (`g = i+1`) and the
    Liouville constants (`g = c^{i·i!}`).

So the golden/disc-5 structure attaches to the **det-one floor**, not to the `W = d`
line itself; "dyadic" is not the repo-supported name — the natural name is
**golden / √5 / disc-5 / `SL₂(ℤ)`** (the `2k`-doubling of `rcut` is the only genuinely
*dyadic* ingredient, and it is metric, not algebraic).  This is the first correction.

## What the repo already contains on the order-3 side

The Eisenstein structure is **already formalized** (CayleyDickson integer track):
`CayleyDickson/Integer/ZOmega*` — `ℤ[ω]`, `ω² + ω + 1 = 0`, norm
`normSq u = a² − ab + b²` (**discriminant `−3`**), unit group **order `6 = NS·NT`**
(`ZOmegaUnits.units_count_eq_six`).  Plus `AlgebraicGeometry.dual_fillings_sum_eq_neg_eisenstein`
(`χ-sum = −6`) and the mod-6 = mod-2 × mod-3 "Eisenstein 6th-roots walk" (`Mod213`).
So the **order-3 / hexagonal reference exists** in 213 — on the algebra side.

What does **not** exist (and is *explicitly* declared out of scope in
`probe_twist_conic.md`): elliptic curves, Weierstrass equations, the j-invariant,
modular forms, complex multiplication.  "the elliptic/modular production … is a
separate, higher edifice. Nothing in this repo touches it."

## The precise content that survives — discriminant sign dictates line vs curve

The intuition "Eisenstein appears as a *curve*, not a *line*" is **correct, with a
reason**, and the reason is the **sign of the discriminant**:

  - **golden `m² − mk − k²`, disc `+5 > 0`** — *indefinite* (real quadratic):
    `Q(1,0) = +1`, `Q(1,1) = −1`.  Level sets are **hyperbolas** (unbounded); the unit
    group of `ℤ[φ]` is **infinite** (`φⁿ`), which *is* the P-orbit — the infinite
    convergent **line**.  Real-quadratic ⟹ a geodesic/line of convergents.
  - **Eisenstein `a² − ab + b²`, disc `−3 < 0`** — *positive-definite* (imaginary
    quadratic): `4(a²−ab+b²) = (2a−b)² + 3b² ≥ 0`, zero only at the origin.  Level sets
    are **ellipses** (bounded); the unit group of `ℤ[ω]` is **finite** (order 6).
    Imaginary-quadratic ⟹ no convergent direction; the natural object is the **lattice
    `ℤ[ω]` and its torus `ℂ/ℤ[ω]`** — which is exactly the period lattice of the **`j = 0`
    elliptic curve** `y² = x³ + b` (CM by `ℤ[ω]`, automorphism of order 6).

So the line/curve dichotomy is forced: **definite norm (disc < 0) ⟹ bounded level sets
⟹ a torus/elliptic curve; indefinite norm (disc > 0) ⟹ unbounded level sets ⟹ a
convergent line.**  Mingu's "Eisenstein ↦ elliptic curve" is the geometric shadow of
`ℤ[ω]` being an imaginary-quadratic order: there is no real continued-fraction
direction, the 6 units sit *on* the torus, and the torus is the `j = 0` curve.

This reframes the conjecture into a repo-native, ∅-axiom-shaped form, dropping the
out-of-scope CM/modular edifice:

## The repo-native conjecture (∅-axiom-shaped)

> **An Eisenstein cross-determinant theory.**  Replace the `ℤ`-convergent pairs
> `(a_i, d_i)` and their `SL₂(ℤ)` cross-determinant `W ∈ ℤ` by **`ℤ[ω]`-convergent
> pairs** and a cross-determinant `W ∈ ℤ[ω]`.  Then:
>   - the **det-one floor** is the order-**6** unit group (`units_count_eq_six`) — the
>     Eisenstein analog of `±1` (the 2 units of `ℤ`, the φ-floor);
>   - because `ℤ[ω]` is imaginary-quadratic (finite units), there is **no** `W = d`
>     convergent *line*; the reference is the **lattice `ℤ[ω]` itself = the `j = 0`
>     elliptic curve's period lattice**.

Concrete ∅-axiom targets (in increasing reach):
  1. `eisenstein_norm_posdef` — `4·normSq u = (2·re − im)² + 3·im²`, hence `normSq ≥ 0`,
     `= 0 ↔ u = 0` (the bounded-level-set / "curve not line" core).  Blocked only by the
     lack of an ∅-axiom Int-ring tactic (`ring` is unavailable / axiom-dirty here); needs
     a manual Int expansion or an `Int213` poly-identity helper analogous to
     `Meta/Nat/PolyNat.poly_id`.
  2. `golden_form_indefinite` — `Q(1,0) = 1`, `Q(1,1) = −1` (trivial, decide).
  3. the dichotomy theorem: definite (Eisenstein, disc −3) vs indefinite (golden, disc
     +5), tying the unit-count (6 vs ∞) to bounded-vs-unbounded level sets.
  4. an `ℤ[ω]`-cross-determinant `W = a_{i+1}d_i − a_i d_{i+1} ∈ ℤ[ω]` with the
     det-(unit) floor characterised by `ZOmegaUnits`.

The **full** elliptic-curve / CM / modular layer remains out of scope (per
`probe_twist_conic.md`); what is reachable is the **lattice reference** (`ℤ[ω]`, already
built) and the **discriminant-sign dichotomy** that explains the line-vs-curve shape.

## One-line summary

The `W = d`/det-one references are the **real-quadratic (disc > 0, golden, infinite
units) → convergent-line** side; the Eisenstein reference is the **imaginary-quadratic
(disc −3, definite, 6 units) → torus = `j = 0` elliptic-curve-lattice** side.  213
already carries both (`ProbeTwistConic` vs `ZOmega`); the line-vs-curve dichotomy is the
sign of the discriminant, and *that* — not the CM/modular machinery — is the ∅-axiom
heart of the conjecture.
