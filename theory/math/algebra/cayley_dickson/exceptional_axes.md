# Exceptional Axes (E₆ E₇ E₈ over 213)

**Status**: Closed.  The exceptional binary-polyhedral rungs `E₆, E₇, E₈`
and their quadratic seeds `{√−NS, √NT, √(NS+NT)} = {√−3, √2, √5}` are
derived end-to-end — `∅`-axiom — from the atomic pair `{NS, NT} = {3, 2}`
and the single integer map `D(x) = x² − NT`.  13 Lean files, ~65 PURE
theorems.

## Overview

> **The seeds are not chosen, and not imported.**  Starting from the
> Möbius signature `P = [[2,1],[1,1]]` (trace `NS = 3`, det `1`, disc
> `NS+NT = 5`) and nothing else, the three exceptional rungs fall out as
> the three dynamical regimes of one trace-doubling map, indexed by the
> atomic triple `{NT, NS, NS+NT}`.  The surds `√2, √5, √−3` are the
> `ℝ`-eigenvalue shadows of three integer recurrences; over `ℕ` they
> dissolve.

The classical fact is that the finite subgroups of `SU(2)` are
`A`(cyclic), `D`(binary dihedral), `E₆ = 2T`, `E₇ = 2O`, `E₈ = 2I`
(binary tetra/octa/icosahedral), with coefficient rings `ℤ`, `ℤ[√2]`,
`ℤ[φ] = ℤ[√5]`.  213 asks the sharper question — *why these three, why
these surds* — and answers it without leaving the integers:

```
disc P = NS+NT          (the 5-floor; the only number the P-engine yields)
   │
   ├─ E₇/√2 is NOT disc-forced   (two_not_a_discriminant: t²−4d ≢ 2 mod 4)
   │      → the seed is a TRACE, not a discriminant
   │
   ├─ φ(n) crystallographic keystone   (rational trace ⟺ n∈{1,2,3,4,6})
   │      → quadratic trace first at φ=4: orders {5,8,10,12} (the 4D layer)
   │
   ├─ spherical filter   (1/p+1/q+1/r>1 ⟺ Platonic)
   │      → exactly 3 rotation groups: (2,3,n), n∈{3,4,5}={NS,NS+1,NS+NT}
   │
   ├─ seed re-entry   (the same NS+NT at matrix/field/quaternion scale)
   │      → √2 = the morphological residue of the unit (trace(g₈)²=trace 1=NT)
   │      → trace-doubling map D(x)=x²−NT, unit = fixed core
   │      → two engines, one map: elliptic(√2) | hyperbolic(√5) split at |x|=NT
   │
   ├─ axis trichotomy   (2-axis √NT, 3-axis Eisenstein ω, 2+3-axis golden φ)
   │      → 4+ axes are composites: {NT,NS,NS+NT}={2,3,5} = primes of |2I|=120
   │
   └─ over ℕ the surds dissolve   (√D = ℝ-eigenvalue shadow of an integer matrix)
          → three companion matrices, disc-sign = real(grow) | imaginary(periodic)
```

Nothing is an extrapolation: `ℤ[√2]`, `ℤ[ω]`, `ℤ[φ]` are 213-internal
constructions, and every step is a closed integer computation or a pure
structural proof.

## Lean source

- **Umbrella**: `lean/E213/Lib/Math/Algebra/CayleyDickson.lean` (imports all
  Tower files)
- **Sub-tree**: `lean/E213/Lib/Math/Algebra/CayleyDickson/Tower/`
- **∅-axiom status**: **0 DIRTY** — every master theorem reports
  `#print axioms … → "does not depend on any axioms"`.

| # | File | Lines | Capstone theorem |
|---|---|---:|---|
| 15 | `DiscForcingObstruction.lean` | 130 | `disc_forcing_splits_at_E7` |
| 16 | `ExceptionalTraceSeed.lean` | 110 | `exceptional_trace_seeds` |
| 17 | `CyclotomicTraceDegree.lean` | 110 | `why_root_two_and_root_five` |
| 18 | `PlatonicSchlafliFilter.lean` | 120 | `why_exactly_three` |
| 19 | `QuadraticFieldDiscriminant.lean` | 105 | `seed_reentry` |
| 20 | `UnitResidueRootTwo.lean` | 165 | `unit_morphological_residue` |
| 21 | `TraceDoublingMap.lean` | 140 | `unit_is_fixed_core` |
| 22 | `TwoEnginesDichotomy.lean` | 105 | `two_engines_one_map` |
| 23 | `AxisSeedTrichotomy.lean` | 130 | `axis_seed_trichotomy` |
| 24 | `AxisComposition.lean` | 110 | `axes_from_three_components` |
| 25 | `PMatrixArithmeticBridge.lean` | 125 | `P_matrix_bridge` |
| 26 | `NaturalTowerForm.lean` | 130 | `natural_tower_form` |
| 27 | `ThreeAxisRecurrence.lean` | 130 | `three_axes_surd_free` |

## Narrative

### 1. The disc-forcing obstruction

The `E₈` seed is *forced*: `√5 = √(disc P)`, `disc P = trace² − 4·det =
9 − 4 = 5 = NS+NT`.  The Eisenstein `E₆` seed `√−3` is likewise a
discriminant (`1 − 4 = −3`).  Does the same mechanism force `E₇`'s
`√2 = √NT`?

**No, and there is a sharp obstruction.**  An integer `2×2` discriminant
is `t² − 4d`, and `t² ≡ 0` or `1 (mod 4)`, so `t² − 4d ≢ 2 (mod 4)` —
never `2`.

> `two_not_a_discriminant (t d : Int) : t*t − 4*d ≠ 2`

proved `∅`-axiom by parity (`t·t = ↑|t|²` via `Int.natAbs_mul_self`;
even/odd of `|t|` forces `4·X = 2` resp. `4·X = 1`, both impossible since
`4·X = 2·(2·X)` and `2·Y ≠ 1`).  The naive value `NT = 2` is *not* a
discriminant; `disc_forcing_splits_at_E7` records that `E₈`(`5`) and
`E₆`(`−3`) are discriminants while `E₇`(`2`) is not.

### 2. The seed is a trace, not a discriminant

If the discriminant misses `E₇`, what *is* the mechanism?  The seed of
each rung is the **trace** (`= 2·Re = 2cos θ`) of its defining rotation —
the diagonal invariant dual to the discriminant.

> `octahedral_trace_sq_eq_NT : trace(g₈)² = NT`       (order-8, `2cos(2π/8) = √2`)
> `icosian_trace_seed_eq_NS_NT : (2·trace(g₅)+1)² = NS+NT`   (order-5, `2cos(2π/5) = φ−1`)

The bridge is the **crystallographic restriction**, made rigorous via the
Euler totient (`φ` defined `∅`-axiom by `NatHelper.gcd213`, since core
`Nat.gcd` leaks `propext`):

> `crystallographic_restriction : {n ≤ 12 : φ(n) ≤ 2} = {1,2,3,4,6}`

Rational trace (`φ ≤ 2`) ⟺ orders `{1,2,3,4,6}` (the `GL(2,ℤ)`-realisable
rotations, `E₆` among them).  Quadratic trace first appears at `φ(n) = 4`
(orders `{5,8,10,12}`) — the 4D quaternion layer where `2I, 2O` live.
`φ(5) = φ(8) = 4 = 2²` is exactly the quaternion dimension, which is why
`E₇/E₈` sit one Cayley–Dickson doubling above the 2D matrix layer.

### 3. Why exactly three

The `φ`-census admits four quadratic orders `{5,8,10,12}` into 4D, but
there are only three exceptional rungs.  The cut to three is the
**spherical condition** `1/p + 1/q + 1/r > 1`:

> `schlafli_platonic_five : {(p,q) : (p−2)(q−2) < 4} = {(3,3),(3,4),(4,3),(3,5),(5,3)}`
> `spherical_triangle_233n : {(2,3,n) finite} = {n : 5n+6 > 6n} = {3,4,5}`

Five Platonic solids collapse (by duality) to three rotation groups
`A₄, S₄, A₅` of orders `12, 24, 60`, binary covers `24, 48, 120 =
(NS+1)!, 2(NS+1)!, (NS+NT)!`.  The triangle indices `{3,4,5} =
{NS, NS+1, NS+NT}` are the atomic numbers; the boundary `(p−2)(q−2) = 4`
(`{4,4},{3,6},{6,3}`, i.e. `1/2+1/3+1/6 = 1`) is the Euclidean affine `Ê`
edge where finiteness ends.

### 4. Seed re-entry and the unit's residue

The number `NS+NT = 5` re-enters as its own operand at three scales — the
213 expansion engine (`diag_self_applies`) at the seed-number level:

> `seed_reentry`:  `disc P = 5`  (2D matrix)  `= fundDisc ℚ(√5)`  (number field)  `= (2·trace(g₅)+1)²`  (4D quaternion)

For `E₇`, `√2` is the **morphological residue of the unit itself**.  The
identity quaternion has trace `2 = NT`, and:

> `root_two_is_sqrt_unit_trace : trace(g₈)² = trace(1) = NT`
> `root_five_is_not_sqrt_unit_trace : trace(g₅)² ≠ trace(1)`   (uniquely √2)

`g₈` sits on the **dyadic self-square-root tower** `1 →² −1 →² i →² g₈`
(orders `2⁰,2¹,2²,2³`, traces `2,−2,0,√2`); `√2 = |1+i|` is the ramified
prime over `NT` in `ℤ[i]` (`(1+i)² = 2i`, `N(1+i) = NT`).  The squaring
map `g ↦ g²` acts on traces as `D(x) = x² − NT`; iterating `D` contracts
the dyadic tower onto the unit trace `NT` (its fixed point), with the
order-`3`/`E₆` trace `−1` as the *odd* fixed point:

> `unit_is_fixed_core`:  `trace(g²) = D(trace g)`,  `D(NT) = NT`,  fixed points `{−1, NT}`.

### 5. Two engines, one map

`D(x) = x² − NT` drives the `P`-engine too: `trace P = NS`, and
`D(trace P) = NS² − NT = 7 = trace(P²)`.  But `|trace P| = NS > NT`, so
the `P`-orbit **escapes** — `3 ↦ 7 ↦ 47 ↦ 2207`, hyperbolic — while the
unit's dyadic orbit stays bounded (elliptic):

> `two_engines_one_map`:  `|x| ≤ NT` elliptic (unit, seed `√NT`); `|x| > NT` hyperbolic (`P`, `trace P = NS = NT+1`, seed `√(NS+NT)`).

The two seeds are the residues of the two regimes of the one map, split
at the unit trace `NT`; `NS = NT + 1` places `P` exactly one step into the
hyperbolic side.

### 6. The axis trichotomy and composition

The three atomic quantities index three axes, three algebraic numbers,
three dynamical types:

| axis | radicand | algebraic # | min poly | `D`-type | rung |
|---|---|---|---|---|---|
| `2` | `NT` | `√2` (bare) | `x² − NT` | even fixed `+2` (unit) | `E₇` |
| `3` | `−NS` | `ω` (Eisenstein) | `x² + x + 1` (`Φ₃`) | odd fixed `−1` (ord 3) | `E₆` |
| `2+3` | `NS+NT` | `φ` (golden) | `x² − x − 1` | hyperbolic escape (`P`) | `E₈` |

> `axis_seed_trichotomy` — the three radicands are the atomic triple.

Axes `≥ 4` are **composites**: `{NT, NS, NS+NT} = {2,3,5}` are the prime
factors of `|2I| = 120 = 2³·3·5`; every polyhedral order is `{2,3,5}`-
smooth (the first non-smooth `7` is the first absent order); and since
`φ` is multiplicative, composite trace fields are the **compositum** of
the prime-axis ones (`φ(6)=φ(2)φ(3)`, `φ(15)=φ(3)φ(5)`, …):

> `axes_from_three_components` — the three generate the whole axis structure.

### 7. Over ℕ the surds dissolve

The `√D` are artifacts of the `ℤ`/`ℝ` frame.  Over `ℕ` each seed is a
**recurrence** (companion matrix), surd-free; the surd is the
`ℝ`-eigenvalue (Binet) shadow:

| axis | matrix | min poly | `trace Mⁿ` | disc | type |
|---|---|---|---|---|---|
| `2` | `[[NT,1],[1,0]]` | `x²−NT·x−1` | `2,2,6,14,34` | `NT²+4 = 8` | Pell (real) |
| `3` | `[[0,−1],[1,−1]]` | `x²+x+1` | `2,−1,−1` (per 3) | `−NS = −3` | cyclotomic (imag) |
| `2+3` | `[[2,1],[1,1]] = P` | `x²−NS·x+1` | `2,3,7,18,47` | `NS+NT = 5` | Lucas (real) |

> `lucas_is_trace_P_pow : L_n = trace Pⁿ`   (`√5` only in eigenvalues `φ²,φ⁻²`)
> `disc_sign_is_field_type` — `disc > 0` real/growing; `disc < 0` imaginary/periodic (`M³ = I`)
> `three_axes_surd_free` — three integer matrices, coefficients the atomic `{NT, NS}`.

A `√D` is a "root" precisely because `D` is **not** a perfect square over
`ℕ` (`seeds_are_nonsquare_residues`: the radicand lies strictly between
consecutive squares, or is negative) — the surd is the residue of the
square root `ℕ` does not contain.  The exact form is the integer matrix;
`disc`-sign splits the real (`P`-engine, growing) and imaginary
(`ω`-engine, periodic) worlds.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `two_not_a_discriminant` | `DiscForcingObstruction` | `t² − 4d ≠ 2`: `√2` is no matrix discriminant |
| `disc_forcing_splits_at_E7` | `DiscForcingObstruction` | `E₈`(`5`), `E₆`(`−3`) are discriminants; `E₇`(`2`) is not |
| `octahedral_trace_sq_eq_NT` | `ExceptionalTraceSeed` | `trace(g₈)² = NT`: the `E₇` seed is a trace |
| `crystallographic_restriction` | `CyclotomicTraceDegree` | rational trace ⟺ order `∈ {1,2,3,4,6}` |
| `why_exactly_three` | `PlatonicSchlafliFilter` | the spherical filter selects `(2,3,n)`, `n∈{3,4,5}` |
| `seed_reentry` | `QuadraticFieldDiscriminant` | `NS+NT` at matrix/field/quaternion scale |
| `unit_morphological_residue` | `UnitResidueRootTwo` | `√2 = √(trace 1)`, uniquely; `= |1+i|` |
| `unit_is_fixed_core` | `TraceDoublingMap` | `D(x) = x²−NT`, unit = fixed point |
| `two_engines_one_map` | `TwoEnginesDichotomy` | elliptic `√2` / hyperbolic `√5`, split at `NT` |
| `axis_seed_trichotomy` | `AxisSeedTrichotomy` | 3 axes = bare `√NT` / Eisenstein `ω` / golden `φ` |
| `axes_from_three_components` | `AxisComposition` | `{2,3,5}`-smooth; higher axes are composites |
| `three_axes_surd_free` | `ThreeAxisRecurrence` | 3 integer matrices; `disc`-sign = field type |

## Companion chapter

The meta-CD-tower, A-D-E census, and binary-polyhedral-group material
feed `algebra_tower.md`; this chapter derives the exceptional axes.

## Open frontier

- **`E₇` `P`-forcing tightness.**  `√2` is trace-anchored and
  disc-*excluded* (proved); its field discriminant `8` *is* a matrix
  discriminant but never `disc P`.  Whether a *different* 213-internal
  mechanism forces octahedral specifically over `ℤ[√NT]` (beyond
  seed-atomicity) is open — but bounded: the no-exterior frame removes
  any falsification worry (there is no outside for `√2` to come from).
- **The transcendental layer.**  The `3`-axis real/transcendental shadow
  (analogue of `e`/`π`) is the equianharmonic Eisenstein period (`j = 0`
  CM by `ℤ[ω]`, a `Γ(1/3)`-value).  Periods are not `∅`-axiom integer
  data; only the algebraic skeleton is formalised.
- **Beyond the `7`-gap.**  The hyperbolic/affine `Ê` region past the
  spherical wall (`1/p+1/q+1/r ≤ 1`) is untouched here.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Algebra.CayleyDickson
python3 tools/scan_axioms.py Lib/Math/Algebra/CayleyDickson/Tower
```

## Citation guidance

- ✅ `theory/math/algebra/cayley_dickson/exceptional_axes.md` (this chapter,
  primary narrative for `E₆E₇E₈` derivation)
- ✅ `theory/math/algebra/cayley_dickson/algebra_tower.md` (sibling: the CD
  algebra tower / 4-row type matrix)
