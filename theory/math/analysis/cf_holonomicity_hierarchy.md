# The continued-fraction holonomicity hierarchy — Hurwitzian, and the π frontier

**Status**: Framework closed; the top tier's π-membership is the documented open frontier.
Source of truth (all ∅-axiom): `lean/E213/Lib/Math/Cauchy/HurwitzianCF.lean` (21 PURE / 0
dirty), on the `polyDepth` divergence-ladder of `Cauchy/DepthPRecursive`.

## Overview

A real's continued fraction carries a **third spiral-layer reading**, distinct from the two
of `spiral_coordinate_classification.md`.  The convergent cross-determinant is the det-one
floor `W² = 1` for *every* real (`ContinuedFractionFloor.cf_det_sq`); the **partial-quotient
sequence** `(aᵢ)` itself is the new object, and its finite-difference depth stratifies the
reals by how regular their continued fraction is — a stratification orthogonal to
algebraic/transcendental and (conjecturally) to the irrationality measure.

A real is **Hurwitzian** (Hurwitz; e, e², tan 1, …) when `(aᵢ)` is eventually
*quasi-polynomial* — polynomial on each residue class modulo some period `p`.  This is the
classical formal handle on "P-recursive / holonomic partial quotients".

  | tier | class | `(aᵢ)` | example |
  |---|---|---|---|
  | 0 | quadratic irrational | eventually periodic | φ = [1;1,…], √2 = [1;2,2,…] |
  | 1 | Hurwitzian, aperiodic | quasi-polynomial | e = [2;1,2k,1,…], tan 1 = [1;1,1,3,1,5,…] |
  | top | non-Hurwitzian | not quasi-polynomial | `2ⁿ` (still C-finite!); π (conjectured) |

## Lean source

| Theorem | Statement (informal) |
|---|---|
| `QuasiPolyCF p a` | `a` is polynomial (finite difference-depth) on each residue class mod `p` |
| `periodic_quasipoly` | tier 0: eventually-periodic CF ⟹ quasi-polynomial (quadratic irrationals) |
| `e_cf_quasipoly` | tier 1: e's `[2;1,2k,1]` pattern is `QuasiPolyCF 3` |
| `tan_cf_quasipoly` | tier 1: tan 1's `[1;1,1,3,1,5,…]` is `QuasiPolyCF 2` |
| `polyDepth_diff_recurrence` | `polyDepth d s ⟹ Δ^{d+1} s = 0` (constant-coefficient recurrence) |
| `quasipoly_section_recurrence` | each residue section of a Hurwitzian CF is C-finite |
| `geometric_not_quasipoly` | `2ⁿ ∉ QuasiPolyCF p` for any `p` — the top tier is inhabited |
| `geom_infinite_depth`, `liftK_geo` | a geometric `c·bᵏ` (`b ≥ 2`) has no finite divergence depth |
| `ePQ_linear_bound`, `tanPQ_linear_bound` | e, tan 1 have linearly-bounded partial quotients ⟹ (cited) `μ = 2` |

Reusable pure infrastructure born here: `pow_mul_pure`, `mul_sub_pure_le`, `polyDepth_congr`,
`resP_mod`, `res3_div` (each replacing a `propext`/`Quot.sound`-leaking core lemma).

A companion file `Cauchy/PositiveFloorUnbounded.lean` (11 PURE) adds the unboundedness side:

| Theorem | Statement (informal) |
|---|---|
| `positive_floor_unbounded` | a positive *constant* top finite-difference (`polyDepth (m+1) s`, `Δ^{m+1}s(0) ≥ 1`) ⟹ `s` unbounded, with explicit witness `n` for every bound `B` |
| `bounded_floor_zero` | (decidable `ℕ` contrapositive) bounded depth-`(m+1)` sequence ⟹ `Δ^{m+1}s(0) = 0` |
| `ePQ_unbounded` | e's partial quotients are unbounded — its `2k+2` section has positive top difference, so `positive_floor_unbounded` fires |

## Narrative

### The quasi-polynomial class

`QuasiPolyCF p a := ∀ r < p, ∃ d, polyDepth d (k ↦ a(p·k + r))`.  Each residue class is an
integer-valued (rational-coefficient, the class `polyDepth` characterises) polynomial in the
block index.  The literature's *Hurwitzian* number is exactly an *eventually*
quasi-polynomial CF; `QuasiPolyCF` is the pure-from-offset core, and the full class is
`QuasiPolyCF` after a finite prefix.

### Tier 0 — periodicity

A periodic partial-quotient sequence has each residue section constant (`periodic_const_subseq`),
hence depth 0, hence `QuasiPolyCF` (`periodic_quasipoly`).  By Lagrange's theorem (cited) the
eventually-periodic CFs are exactly the quadratic irrationals, so every quadratic irrational
is Hurwitzian of the simplest kind — the floor of the hierarchy.

### Tier 1 — e and tan 1

e = [2; 1, 2, 1, 1, 4, 1, 1, 6, …]: writing `ePQ i = a_{i+1}` (the fractional partial
quotients, `a₀ = 2` held outside), the pattern is `2k+2` on residue `1 (mod 3)` and `1`
elsewhere.  The three residue sections are constant `1` (depth 0), the linear `2k+2` (depth
1), and constant `1` (depth 0); so `e_cf_quasipoly : QuasiPolyCF 3 ePQ`.  This is the
folklore implication "Hurwitzian ⟹ holonomic" — true but unstated in the literature — made
an explicit ∅-axiom theorem.  tan 1 = [1; 1, 1, 3, 1, 5, 1, 7, …] gives a cheaper second
witness (`tanPQ i = if i % 2 = 0 then 1 else i`, `QuasiPolyCF 2`: the odd residue is the
linear `2k+1`), confirming the tier is not an e-only artifact.

That these explicit sequences equal the actual continued fractions of e and tan 1 is
Euler/Hermite (cited, not re-proven); the 213 content is the quasi-polynomial structure of
the sequence.

### The holonomicity certificate, and what "holonomic" means here

`polyDepth d s ⟹ Δ^{d+1} s = 0` (`polyDepth_diff_recurrence`): a degree-`d` polynomial
sequence satisfies the homogeneous **constant-coefficient** recurrence given by the
`(d+1)`-th finite difference.  So each residue section of a Hurwitzian CF is C-finite
(`quasipoly_section_recurrence`); a finite interleaving of C-finite sections is P-recursive
by the classical interlacing closure (cited).  Quasi-polynomial ⟹ holonomic, section by
section.

The converse fails, and the gap is the crux of honesty here:
`QuasiPolyCF ⊊ C-finite ⊊ holonomic`, **strictly**.

### The top tier is inhabited — and strictly inside holonomic

`geometric_not_quasipoly`: `2ⁿ` is not `QuasiPolyCF p` for any `p`.  The residue-`0` section
is `k ↦ 2^{p·k} = (2^p)^k`, geometric with base `≥ 2`; `liftK_geo` shows the divergence
ladder keeps it geometric (`Δʲ(c·bᵏ) = Aⱼ·bⁿ`, `Aⱼ ≥ 1`), so at every lift level the value
at `0` is below the value at `1` (`geom_infinite_depth`), and it never reaches the constant
floor.  No finite difference-depth, so no `p` works.

Yet `2ⁿ` is C-finite (`2ⁿ⁺¹ = 2·2ⁿ`), hence holonomic.  So the "non-Hurwitzian" top tier is
non-empty *inside* the holonomic class: being non-Hurwitzian is **strictly weaker** than
being non-holonomic.  This is the precise altitude of the π frontier.

### Orthogonality

The CF-holonomicity tier separates e (tier 1) from a geometric Liouville-type CF (top tier)
without leaving the holonomic class, and is conjectured to separate e from π where the
irrationality measure does not (`μ(e) = 2`; `μ(π) = 2` conjectured, `≤ 7.103` proven —
Zeilberger–Zudilin 2020).  It is a reading of regularity orthogonal to the cross-determinant
depth and the unit-axis of the spiral classification.

## Open frontier

The headline is the **non-holonomicity of π's continued fraction** — that `(aᵢ)` satisfies
no linear recurrence with polynomial coefficients.  Classically open; not closable ∅-axiom.
Two honest layers sit below it:

  - **π non-Hurwitzian** (`¬ ∃ p, QuasiPolyCF p (πCF)`) — weaker than non-holonomicity, and
    likely true for cheap statistical reasons (π's partial quotients are conjecturally
    Gauss–Kuzmin distributed, unbounded with a heavy tail).  Still open, but not the real
    target.
  - **π non-holonomic** — the real target, *strictly above* non-Hurwitzian (a sequence can
    be non-Hurwitzian yet holonomic, as `2ⁿ` shows).

The credible route is the **Flajolet–Gerhold–Salvy asymptotic obstruction**: a holonomic
sequence has asymptotics of the restricted form `C·ρ⁻ⁿ·n^θ·(log n)^κ`, against which π's
Gauss–Kuzmin statistics are conjecturally incompatible — but this is itself conditional on
π being Gauss–Kuzmin normal, which is also open.  A second obstruction is **Klazar's growth
bound** (holonomic ⟹ `|aₙ| ≤ cⁿ·(n!)^d`): super-`(n!)^d` growth ⟹ non-holonomic — the route
to a genuinely *non-holonomic* witness above the merely *non-Hurwitzian* `2ⁿ`.
Adamczewski–Bugeaud prove the related statement that an algebraic number of degree `≥ 3`
cannot have an *automatic* continued fraction; the holonomic analogue for π is beyond current
methods.

### Where the difficulty is localized — the boundedness frontier

Whether π's partial quotients are **bounded** is itself **open** (not even a sharply-stated
conjecture; unboundedness is only the Gauss–Kuzmin *heuristic*, and π is not known to be
Gauss–Kuzmin normal).  This open boundedness is exactly where the difficulty sits.  *If* π's
partial quotients were bounded, π would be non-holonomic by an elementary route — bounded +
holonomic ⟹ eventually periodic (a classical fact for integer P-recursive sequences, via the
mod-`m` periodicity of the polynomial recurrence coefficients; Garrabrant–Pak) ⟹ quadratic
irrational (Lagrange) ⟹ contradiction with π transcendental.  Since π's partial quotients are
*expected unbounded*, this elementary route is unavailable: any proof of π's non-holonomicity
must engage the unbounded growth of the partial quotients **directly**.  `PositiveFloorUnbounded`
proves the ∅-axiom nucleus of this picture — a genuine positive-degree polynomial section
*forces* unbounded partial quotients (`ePQ_unbounded` for e) — while deliberately **not**
proving "bounded ⟹ eventually constant", which over `ℕ` is the monotone-sequence principle,
equivalent to the limited principle of omniscience (LPO; Mandelkern 1988), hence not ∅-axiom.

### Relationship to the irrationality measure

The irrationality measure `μ(x) = 2 + limsupₙ (ln a_{n+1} / ln qₙ)` is a coarse single
number — a limsup that sees only the worst-case partial quotients.  Three different things
sit in this framework:

  - the **rate modulus** `N(m,k)` (`Real213/RateModulus`) is the irrationality-measure
    *function* `ψ(q)`, of which μ is the limsup-collapse — genuinely **finer** than μ (φ with
    `N = 2k` and e with `N = k+2` share `μ = 2` but have different moduli);
  - the **divergence depth** is the order of the holonomic recurrence of a *presentation* —
    **orthogonal** to μ and presentation-dependent (π is depth 1 via its CF, depth 6 via
    Wallis), so it does not separate numbers;
  - the **CF-regularity tier** is the component that genuinely separates e from π, which μ
    cannot.

The bridge **polynomially-bounded partial quotients ⟹ μ = 2** (classical, exact) has its
∅-axiom half here for the tier-1 witnesses: `ePQ_linear_bound` (`ePQ i ≤ 2i+2`) and
`tanPQ_linear_bound` (`tanPQ i ≤ i+1`) give linear bounds, whence (cited) `μ(e) = μ(tan 1) =
2` directly from the quasi-polynomial structure.  The implication is one-directional (`μ = 2`
does not force bounded partial quotients).  The general `QuasiPolyCF ⟹ polynomially-bounded`
would need the discrete Newton–Gregory bound, delicate over `ℕ` truncated subtraction.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Cauchy.HurwitzianCF
cd ..
python3 tools/scan_axioms.py E213.Lib.Math.Cauchy.HurwitzianCF
```
Reports `21 pure / 0 dirty`.
