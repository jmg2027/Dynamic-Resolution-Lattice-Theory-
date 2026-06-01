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
  1. `eisenstein_norm_posdef` — **DONE / LANDED ∅-axiom**
     (`CayleyDickson/Integer/EisensteinSignature`, 9 PURE):
       - `sq_nonneg (a : Int) : 0 ≤ a*a` — PURE by constructor cases (`ofNat`:
         `Int.ofNat_nonneg (n*n)`; `negSucc`: `Int.negSucc_mul_negSucc`), avoiding
         the propext-dirty `Int.le_total`.
       - `two_eisForm` — `(a²−ab+b²) + (a²−ab+b²) = a² + b² + (a−b)²` proved by the new
         **bivariate `Int` reflection prover** `Meta/Int213/PolyInt2` (`poly_id2`,
         22 PURE — two Horner layers, `X` over `Y`-polynomials, with a `neg` constructor
         for subtraction; the `Int` analog of `Meta/Nat/PolyNat`).  This is the piece
         that was blocked — built as reusable infrastructure (the repo previously had
         **no** pure `Int` ring tactic; `quad_norm` is `simp`+`omega`-dirty).
       - `eisForm_nonneg` / `eisenstein_norm_nonneg : 0 ≤ normSq u` — sum-of-three-squares
         (`sq_nonneg`) + `Int213.nonneg_of_add_self`.
       - `golden_indefinite` (`goldenForm 1 0 = 1`, `1 1 = −1`) + `signature_dichotomy` —
         Eisenstein **definite** (`∀ a b, 0 ≤ eisForm a b`) vs golden **indefinite**
         (`∃, < 0`).  Definite ⟹ bounded level sets ⟹ curve; indefinite ⟹ unbounded ⟹
         line.  The ∅-axiom heart of the conjecture is now a theorem.
  2. `golden_indefinite` + `signature_dichotomy` — DONE (same module): definite
     (Eisenstein, disc −3) vs indefinite (golden, disc +5).  And anisotropy
     `eisenstein_norm_zero` (`normSq u = 0 → u = 0`) + `eisenstein_norm_posdef` (full
     positive-definiteness) — DONE.
  3. **NEXT — the det-one floor = the 6 units, with a *pure* multiplicative norm.**  The
     Eisenstein analog of φ's Cassini floor (`W = ±1` = the 2 units of `ℤ`): the norm-1
     elements of `ℤ[ω]` are exactly the **6 units** (`ZOmegaUnits.units6_normSq_one` +
     `units_count_eq_six` = `NS·NT`, both PURE).  What makes them a *group* (a det-one
     floor) is **norm multiplicativity** `normSq (u·v) = normSq u · normSq v`
     (`ZOmegaDomain.normSq_mul`) — which is currently **`propext`-dirty** (it routes
     through `quad_norm`).  Two routes to a PURE version:
       (a) a **4-variable** Int reflection prover (one nesting deeper than `PolyInt2`:
           `List⁴ Int`) — `normSq_mul` is a 4-var identity in `(a,b,c,d)`;
       (b) the **conjugate route** — `|uv|² = (uv)(\overline{uv}) = u(v\bar v)\bar u =
           normSq v · (u \bar u) = normSq v · normSq u`, reusing
           `ZOmegaAlgebra213.self_mul_conj'` (`u·conj u = ofInt (normSq u)`) and a
           conjugate anti-hom `conj (u·v) = conj v · conj u` — pure iff those algebra
           lemmas are pure.
     Either lands a pure `normSq_mul`, hence "Eisenstein det-one floor = the 6-unit
     group" ∅-axiom — the genuine Eisenstein analog of the golden det-one floor.

The **full** elliptic-curve / CM / modular layer remains out of scope (per
`probe_twist_conic.md`); what is reachable is the **lattice reference** (`ℤ[ω]`, already
built) and the **discriminant-sign dichotomy** that explains the line-vs-curve shape.

## The stronger conjecture (Mingu Jeong) — the modular-surface / geodesic layer

> Above/below the dyadic reference is not simply convergence/divergence; adding the
> complex dimension of the Eisenstein elliptic curve *narrows the resolution*, the
> dyadic magnitude-decision (`rcut`) is performed in that narrowed resolution, and then
> via the elliptic curve's *modularity* the trajectory rides a *converging* orbit again.

Repo-grounded reading.  This rough language is reaching, precisely, for the **modular
surface `ℍ/SL₂(ℤ)` geodesic-flow picture of continued fractions** (Artin/Series coding):
the cross-determinant `W` is the `SL₂(ℤ)` symplectic area, a convergent sequence is a
geodesic, its `rcut`/continued-fraction digits are the geodesic's symbolic coding.  The
surface has **one cusp** (`∞`, parabolic — genuine divergence, the rationals) and **two
elliptic orbifold points**: order **3** at `ω` (Eisenstein) and order **2** at `i`
(Gaussian) — the "narrowed-resolution" cone points.  Phrase by phrase:

  - "above/below, not merely converge/diverge" → the `SL₂(ℤ)` conjugacy **trichotomy by
    trace**: |trace| > 2 *hyperbolic* (a **closed** geodesic — bounded/recurrent in the
    quotient; the golden `P = [[2,1],[1,1]]`, trace `3`, is the simplest one),
    |trace| = 2 *parabolic* (the cusp — the only **genuine** divergence), |trace| < 2
    *elliptic* (periodic fixed points — Eisenstein order 3, Gaussian order 2).
  - "complex dimension of the Eisenstein curve narrows resolution" → lifting the
    real-line cut to the lattice/torus `ℂ/ℤ[ω]` (the `j=0` curve's periods); at the
    order-3 elliptic point the local chart is an orbifold cone — a finer reading.
  - "modularity ⟹ converging orbit" → the `SL₂(ℤ)` action **folds** the geodesic into
    the compact fundamental domain; the hyperbolic golden geodesic becomes a *closed*
    (bounded, recurrent) orbit, the elliptic points are periodic.  The `j`-map ties this
    to the elliptic curve.

**Honest refinement (the over-reach to drop).**  Modularity does **not** turn a
genuinely divergent real-line trajectory into a convergent one *on the line*.  What is
true: the divergence is **folded**, not erased — it acquires a **bounded representation
in the quotient** (a closed geodesic), exactly as a Dirichlet/L-series that diverges in
a half-plane is *defined* there by analytic continuation through the modular functional
equation.  Modularity bounds everything **except** the parabolic cusp, which *is* the
residue (the genuine, irreducible divergence).  So "converging orbit" = bounded orbit
in `ℍ/SL₂(ℤ)`, not convergence of the line-cut.

**213-native reading.**  The overtake (divergent) trajectory is the **residue** —
un-resolved by the real-line Lens.  The Eisenstein/elliptic lift is a *finer Lens* (the
2-D lattice reading); modularity is a **self-covering symmetry** (the order-6 unit
action / the `SL₂(ℤ)` folding) that re-presents the residue as a bounded orbit — the
same self-covering of `DepthCeilingResidue`, now at the scale of the modular surface.
The cusp is where the residue appears in the geodesic picture: the tower with no top.

**Reachable seed (with a scope tension).**  The trace-trichotomy (hyperbolic `P` trace
`3`; an order-3 Eisenstein element, e.g. `[[0,-1],[1,-1]]`, trace `−1`, cube `= I`; an
order-4 Gaussian element `[[0,-1],[1,0]]`, trace `0`) is ∅-axiom (concrete `Int` 2×2
matrices, `decide`).  **But** building a matrix / modular-group layer leans toward the
elliptic-curve/modular edifice the repo *deliberately declines* (`probe_twist_conic.md`);
the repo keeps `P` as a step `Pstep`, not a matrix.  So this seed is recorded, not
built, pending a decision on whether 213 wants the modular-group layer at all.  Out of
∅-axiom reach entirely: geodesic flow, modular forms, the `j`-map, the modularity
theorem, analytic continuation.

## One-line summary

The `W = d`/det-one references are the **real-quadratic (disc > 0, golden, infinite
units) → convergent-line** side; the Eisenstein reference is the **imaginary-quadratic
(disc −3, definite, 6 units) → torus = `j = 0` elliptic-curve-lattice** side.  213
already carries both (`ProbeTwistConic` vs `ZOmega`); the line-vs-curve dichotomy is the
sign of the discriminant, and *that* — not the CM/modular machinery — is the ∅-axiom
heart of the conjecture.
