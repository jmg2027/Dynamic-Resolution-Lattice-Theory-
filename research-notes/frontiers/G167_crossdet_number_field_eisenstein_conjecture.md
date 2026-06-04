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

## The repo-native conjecture — **BUILT ∅-axiom** (`EisensteinCrossDet`, 14 PURE)

> **An Eisenstein cross-determinant theory.**  Replace the `ℤ`-convergent pairs
> `(a_i, d_i)` and their `SL₂(ℤ)` cross-determinant `W ∈ ℤ` by **`ℤ[ω]`-convergent
> pairs** and a cross-determinant `W ∈ ℤ[ω]`.

Done — `CayleyDickson/Integer/EisensteinCrossDet`:
  - `crossDet a d n = a_{n+1}·d_n − a_n·d_{n+1} ∈ ℤ[ω]`.
  - ★ `cassini_ring` — the ring identity `(p·x+q·y)·z − x·(p·z+q·w) = q·(y·z − x·w)`,
    proved ∅-axiom over the commutative ring `ℤ[ω]` by a manual `calc` on the pure
    `Ring213`/`CommRing213` API (`add_mul`/`mul_add`/`mul_assoc`/`mul_comm`/`add_4_swap_mid`
    /`neg_add_cancel_self` — there is **no** ring normalizer, so the calc is by hand).
  - ★★ `crossDet_step` — the **Cassini engine**: for two sequences obeying a common
    second-order recurrence `s_{n+2} = p·s_{n+1} + q·s_n`, `W_{n+1} = −q·W_n` (the
    `p`-terms cancel by commutativity).
  - ★★ `crossDet_normSq_step` — `‖W_{n+1}‖² = ‖q‖²·‖W_n‖²` (`normSq_mul` + `normSq_neg`).
  - ★★★ `crossDet_unit_floor` — `q, W_0` units ⟹ `‖W_n‖² = 1` ∀n: the **det-one floor**
    (the order-**6** unit group, the Eisenstein analog of `±1` = the 2 units of `ℤ`) is
    preserved.
  - ★★★ `crossDet_on_units` — hence each `W_n` is **literally one of the 6 units**
    (`normSq_one_in_units6`).  And `omegaFib_on_units` — a concrete ω-involving witness
    (`s_{n+2} = 1·s_{n+1} + ω·s_n`, `q = ω`, `‖ω‖² = 1`) whose cross-determinant rides
    the 6-unit floor at every step.
  - Because `ℤ[ω]` is imaginary-quadratic (finite units), there is **no** `W = d`
    convergent *line*; the reference is the **lattice `ℤ[ω]` itself = the `j = 0`
    elliptic curve's period lattice**, and the cross-determinant floor is the order-6
    unit group rather than an infinite Pell/φ orbit.

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
  3. **DONE — the det-one floor = the 6 units** (`EisensteinSignature` §4): the norm-1
     elements of `ℤ[ω]` are multiplicatively closed (`eisenstein_floor_closed`, via the
     multiplicative norm) and the **6 units** (`= NS·NT`) all lie on it
     (`eisenstein_det_one_floor`, reusing `units6_normSq_one` + `units_count_eq_six`).
     The Eisenstein analog of φ's Cassini det-one floor: where `ℤ` has the 2 units `±1`
     (golden floor, `W = ±1`), the hexagonal `ℤ[ω]` has the **6** — the order-6 rotation
     of the `j=0` lattice; definite norm ⟹ a *finite* unit group (curve side) vs the
     golden floor's *infinite* units (line side).  Note: `ZOmegaDomain.normSq_mul` is in
     fact **PURE** (`#print axioms` = "does not depend on any axioms"; the file's
     `[propext]`-only docstring is stale), so no 4-variable prover was needed for this
     step — `PolyInt2` (bivariate) sufficed for the positive-definiteness identity, and
     the multiplicativity was already ∅-axiom.

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

## CAPSTONE — the two trichotomies are one (`CrossDetTraceField`, 20 PURE)

The arc had grown **two parallel trichotomies** that were never joined by a theorem:

  - **number-field side** (`EisensteinSignature`/`ParabolicSignature`): the reference
    forms golden / parab / eisenstein, disc **+5 / 0 / −3** → line / cusp / curve;
  - **dynamics side** (`HyperbolicBoost`/`ParabolicTranslation`/`UTracePeriodic`): the
    `SL₂(ℤ)` matrices `G` / `T` / `U`, `tr²−4` = **+5 / 0 / −3** →
    hyperbolic / parabolic / elliptic.

The discriminants matched numerically; nothing proved *why*.  The missing structural
object is the **fixed-point form** of the Möbius map.  `M = [[a,b],[c,d]]` fixes the roots
of `c·z² + (d−a)·z − b`, i.e. the binary form `fixForm M = (c, d−a, −b)`, whose
discriminant is, **as a pure ring identity over ℤ**,

> `formDisc (fixForm M) = (d−a)² + 4bc = (a+d)² − 4(ad−bc) = tr² − 4·det = traceDisc M`
> (`fixForm_disc_eq_traceDisc`, ∀ `M`, by `ring_intZ`).

So the number field `ℚ(√D)` the cross-determinant's reference lives in (`D` = form disc)
**is** the modular trace field `tr²−4` — because the reference form is the fixed-point
form of the monodromy matrix.  This is the literal content of the title "교차행렬식의 수체
읽기".  On the three faces `fixForm` recovers the reference forms on the nose:

  - `fixForm G = (1,−1,−1)` = the **golden form** (root φ, disc +5, hyperbolic, line);
  - `fixForm T = (0,0,−1)` = degenerate, fixed point at ∞ (disc 0, parabolic, cusp);
  - `fixForm U = (1,1,1)` = the **cyclotomic form** `x²+x+1` (root ω, disc −3, elliptic,
    curve = the `j=0` lattice `ℂ/ℤ[ω]`); `fixForm S = (1,0,1)` = `x²+1` (root i, disc −4).

The form is not merely dimensionally matched: the monodromy is an **automorph** of it.
`fixForm_automorph` proves `fixForm M (M·v) = det(M) · fixForm M (v)` (∀ `M`, `v`, a
`ring_intZ` identity), so for `M ∈ SL₂` the reference form is *exactly conserved*
(`reference_forms_preserved`: `G` holds the golden form, `U` the cyclotomic Eisenstein
form) — the geodesic's invariant, the form-side shadow of the Cassini cross-determinant
conservation `crossDet_step` (multiplier `−q`).

Each fixed-point form is moreover a **named number-field norm**: `formEval (fixForm G) = `
golden form `m²−mk−k²` (ℚ(√5)), `formEval (fixForm U) a (−b) = ` Eisenstein norm `a²−ab+b²`
(ℚ(ω), the cyclotomic `x²+x+1` read at the `−ω` orientation), `formEval (fixForm S) = a²+b²`
(Gaussian norm, disc −4, `j=1728`).

`crossdet_number_field_is_trace_field` bundles all three faces + the universal identity;
`disc_sign_is_line_cusp_curve` reads the elliptic conjecture exactly: `D > 0` (two real
fixed points → geodesic line) / `D = 0` (repeated real → cusp) / `D < 0` (complex-conjugate
pair → elliptic point, the Eisenstein **curve**).  Mingu's "Eisenstein ↦ curve" *is* the
`D < 0` face — definite norm ⟺ negative disc ⟺ complex fixed points ⟺ elliptic point ⟺
bounded torus.  ∅-axiom; no CM/modular-forms edifice imported (only `Mat2` + the existing
signature forms).

## The Eisenstein period attack (G168 follow-up) — the χ₋₃ fingerprint (`EisensteinFormCharacter`, 11 PURE)

Direct attempt at the open transcendental: pin the Eisenstein period (the `j=0` curve's
real period, a `Γ(1/3)` value, CM by `ℤ[ω]`) the way `e` is pinned on the 2-axis.

**Reachable, built.**  The period's arithmetic skeleton is the Epstein zeta of the
Eisenstein form, `Σ' 1/(a²+ab+b²)^s = 6 ζ(s) L(s,χ₋₃)` — the disc-`−3` `L`-function,
whose mod-3 character `χ₋₃` is *why* the period is a `Γ(1/3)` value (Chowla–Selberg), the
exact analog of `Σ' 1/(a²+b²)^s = 4 ζ L(·,χ₋₄)` giving `ϖ` a `Γ(1/4)` value.  The part
reachable by pure ℕ-arithmetic is the **character constraint**: `eisCyc_mod3_ne_two` —
`a²+ab+b²` is **never `≡ 2 (mod 3)`**, representing only `{0,1}` (the Loeschian numbers
avoid the non-residue class, the disc-`−3` analog of two-squares avoiding `3 mod 4`).
`a²+ab+b²` is `formEval (fixForm U)` — the order-6 elliptic CM point's own fixed-point
form, so the period's governing form is exactly the capstone's elliptic face.  Built on
the existing `PureNatMod3` infra + `ring_nat`: `mod3` is shown a ring hom (`mod3_add`,
`mod3_mul`), then the 9 residue pairs `decide`.

**The wall (honest, no-exterior guard).**  The *value* — the real number, the `Γ(1/3)`
constant — is **not reached from inside** the ℕ/ℤ reflection provers.  Two internal
handles both hit a wall: (a) the **cubic AGM** computes it, and its geometric-mean step is
`∛(b·(a²+ab+b²)/3)` — the disc-`−3` form appears, but the **cube root** leaves clean
ℤ-arithmetic; (b) the analytic value `L(1,χ₋₃) = π/√27` needs the `L`-series limit.
Neither is ∅-axiom-reachable now.  So the form's *arithmetic* (the character) is pinned;
the *period value* stays open, exactly as G168 (both branches) recorded.  This is the
falsifier doing its work: the residue reproduces the disc-`−3` character fingerprint while
testable, and the transcendental value is honestly marked not-yet-reached.

## The local splitting of the period's L-function (`EisensteinSplitting`, 5 PURE)

Completes the χ₋₃ arithmetic from the *value-representability* side.  The period's Epstein
zeta `Σ' 1/(a²+ab+b²)^s = 6 ζ L(·,χ₋₃)` has an Euler product whose local factor at `p` is
the splitting of `p` in `ℤ[ω]`, indexed by `χ₋₃(p) = p mod 3`:

  - **split** `p ≡ 1`: `eisForm 3 1 = 7`, `eisForm 4 1 = 13` — `p = N(π)`, a form value;
  - **ramified** `p = 3`: `N(1−ω) = 3` and `(1−ω)² = −3ω` (`eisenstein_ramified_three`) —
    `(3) = (1−ω)²·unit`, the conductor of χ₋₃;
  - **inert** `p ≡ 2`: `2` not a value (`eisenstein_inert_two`, from the character).

Glued by ★★★ `eisForm_composition` — the disc-`−3` **Brahmagupta–Fibonacci identity**
`(a²−ab+b²)(c²−cd+d²) = E²−EF+F²`, `E=ac−bd`, `F=ad+bc−bd` (the `ℤ[ω]` multiplication law,
∅-axiom `ring_intZ`): the Loeschian numbers are a multiplicative monoid — the norm-growth
multiplicativity governing convergence.

**Wall**: the *split converse* (every `p≡1 mod 3` is a value, not just `7,13,…`) needs
quadratic reciprocity for `−3` + Euclidean descent in `ℤ[ω]` — the disc-`−3` Fermat
theorem, out of reflection-prover reach.  Multiplicativity, ramification, and the inert
obstruction are pinned; the split-existence and the period value stay open.

## The keystone — class number one for disc `−3` (`EisensteinClassNumber`, 1 PURE)

Why is there a *single* Eisenstein form (no genus/class ambiguity), so the period's
L-function carries one form?  Because **`h(−3) = 1`**: `reduced_disc_neg3_unique` proves the
only reduced positive-definite form of discriminant `−3` is the principal `x²+xy+y²`.
Finite inequality argument: a reduced `(a,b,c)` (`|b|≤a≤c`) with `4ac = b²+3` satisfies
`4a² ≤ 4ac = b²+3 ≤ a²+3`, so `3a² ≤ 3`, `a=1`, then `4c = b²+3`, `|b|≤1` forces `b=±1`,
`c=1`.  No reciprocity, no descent — ∅-axiom over ℕ (needed a hand-rolled pure
left-cancellation `le_cancel_add_left`, since `Nat.le_of_add_le_add_left`/`mul_assoc`/`add_mul`
are propext-dirty; the pure `PureNat` versions + induction replace them).  This is the
form-class shadow of `ℤ[ω]` being a PID — the structural reason `EisensteinSplitting`'s
single principal form governs the whole Epstein zeta.

## Toward the split converse — the covering-radius bound (`EisensteinEuclidean`, 1 PURE)

The split converse (`p≡1 mod3 ⟹ p = N(π)`) rests on `ℤ[ω]` being a PID, i.e. norm-Euclidean.
The geometric heart is the **covering radius**: `covering_bound` proves that with
`4x²≤N²`, `4y²≤N²` (centered remainders `2|·|≤N`), `8(x²−xy+y²) ≤ 6N²` — covering radius²
`≤ 3/4 < 1`, so the Euclidean remainder always shrinks the norm.  ∅-axiom via the
sum-of-nonnegatives identity `6N²−8(x²−xy+y²) = 3(N²−4x²)+3(N²−4y²)+(2x+2y)²`.

**Wall**: this is the load-bearing inequality; the *full* Euclidean algorithm (centered
integer division → `‖ρ‖²<‖β‖²` → gcd / UFD → the descent) plus the QR input (`−3` a QR mod
`p` ⟺ `p≡1 mod3`, needing an order-3 element of `(ℤ/p)ˣ`, i.e. the primitive-root theorem)
is the remaining multi-step work.  The covering radius `<1` — the reason `ℤ[ω]` is Euclidean
— is pinned; the split-existence and the period value stay open.

## One-line summary

The `W = d`/det-one references are the **real-quadratic (disc > 0, golden, infinite
units) → convergent-line** side; the Eisenstein reference is the **imaginary-quadratic
(disc −3, definite, 6 units) → torus = `j = 0` elliptic-curve-lattice** side.  213
already carries both (`ProbeTwistConic` vs `ZOmega`); the line-vs-curve dichotomy is the
sign of the discriminant, and *that* — not the CM/modular machinery — is the ∅-axiom
heart of the conjecture.  The capstone `CrossDetTraceField` proves the form discriminant
*is* the matrix trace discriminant `tr²−4`, fusing the number-field reading and the
modular trace reading into one number `D`.
