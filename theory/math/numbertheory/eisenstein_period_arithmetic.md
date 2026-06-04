# The cross-determinant's number field and the Eisenstein period

**Status**: Closed core, with a recorded open frontier (split converse + period value).

## Overview

A continued-fraction convergent sequence reads the residue through its **cross-determinant**
`W_i = a_{i+1}d_i − a_i d_{i+1}` — the `SL(2,ℤ)` symplectic area of consecutive convergent
vectors.  Which *number field* that reading lives in is the discriminant of the reference
quadratic form the cross-determinant rides.  This chapter closes two facts and records what
stays open:

  1. **The number field is the modular trace field.**  The reference form of an
     `SL(2,ℤ)` element is its *fixed-point form*, and the discriminant of that form equals
     `tr² − 4` of the element — identically, as a ring identity.  So the field `ℚ(√D)` the
     cross-determinant lives in is the trace field of the modular monodromy, and the single
     sign of `D = tr² − 4` is simultaneously the **line / cusp / curve** dial of the number
     theory and the **hyperbolic / parabolic / elliptic** dial of the dynamics.  The
     elliptic (`D < 0`) face is the imaginary-quadratic Eisenstein reading: "the reference
     appears as a curve, not a line."

  2. **The Eisenstein period's arithmetic.**  The disc-`−3` reference (the form
     `a² + ab + b²`, the lattice `ℤ[ω]`, the `j = 0` curve `ℂ/ℤ[ω]`) carries the period
     whose Epstein zeta is `Σ' 1/(a²+ab+b²)^s = 6 ζ(s) L(s, χ₋₃)`.  The arithmetic that
     makes this factorization clean — a single form, governed by the mod-3 character, with a
     multiplicative value monoid — is closed `∅`-axiom: the χ₋₃ representation fingerprint,
     the local split/ramified/inert trichotomy, class number one, and the covering-radius
     bound that makes `ℤ[ω]` Euclidean.

What is **not** closed: the split converse (every `p ≡ 1 mod 3` is a value, needing the
quadratic-residue input and Euclidean descent) and the transcendental period value itself
(a `Γ(1/3)` constant, needing the cubic AGM or the analytic `L(1, χ₋₃)`).  These sit in the
Open frontier section.

## Lean source

| Module | Lean path | ∅-axiom |
|---|---|---:|
| `CrossDetTraceField` | `Lib/Math/NumberSystems/Real213/CrossDetTraceField.lean` | 20 PURE |
| `EisensteinFormCharacter` | `Lib/Math/NumberTheory/ModArith/EisensteinFormCharacter.lean` | 11 PURE |
| `EisensteinSplitting` | `Lib/Math/Algebra/CayleyDickson/Integer/EisensteinSplitting.lean` | 5 PURE |
| `EisensteinClassNumber` | `Lib/Math/Algebra/CayleyDickson/Integer/EisensteinClassNumber.lean` | 1 PURE |
| `EisensteinEuclidean` | `Lib/Math/Algebra/CayleyDickson/Integer/EisensteinEuclidean.lean` | 1 PURE |

Resting on the signature work (`EisensteinSignature`, `ParabolicSignature`,
`EisensteinCrossDet`) and the modular trichotomy (`ModularElliptic`, `HyperbolicBoost`,
`ParabolicTranslation`, `UTracePeriodic`).

## Narrative

### The fixed-point form: number field = trace field

A Möbius map `z ↦ (az+b)/(cz+d)` fixes the roots of `c·z² + (d−a)·z − b`, the binary
quadratic form `fixForm M = (c, d−a, −b)`.  Its discriminant is, as a pure ring identity
over `ℤ`,

  `formDisc (fixForm M) = (d−a)² + 4bc = (a+d)² − 4(ad−bc) = tr(M)² − 4·det(M)`

(`fixForm_disc_eq_traceDisc`, for every `M`).  The cross-determinant's reference form is the
fixed-point form of the monodromy matrix, so its discriminant is the trace discriminant —
not by coincidence, but by this identity.  The monodromy moreover **preserves** its
fixed-point form up to determinant: `fixForm M (M·v) = det(M)·fixForm M (v)`
(`fixForm_automorph`), so on `SL(2,ℤ)` the reference form is the geodesic's conserved
quantity (`reference_forms_preserved`), the form-side shadow of the Cassini cross-determinant
conservation.

On the three conjugacy faces the fixed-point form *is* the named reference form, and its
discriminant is its trace discriminant (`crossdet_number_field_is_trace_field`):

| Face | `M` | `tr²−4` | `fixForm M` | Field | Geometry |
|---|---|---:|---|---|---|
| hyperbolic | `[[2,1],[1,1]]` | `+5` | `(1,−1,−1)` golden, root `φ` | `ℚ(√5)` real-quad | line (geodesic) |
| parabolic | `[[1,1],[0,1]]` | `0` | `(0,0,−1)` cusp at `∞` | `ℚ` | cusp (rational) |
| elliptic | `[[0,−1],[1,1]]` | `−3` | `(1,1,1)` cyclotomic, root `ω` | `ℚ(ω)` imag-quad | curve (torus) |

Each fixed-point form is a named number-field norm: `formEval (fixForm G) = goldenForm`
(`ℤ[φ]`), `formEval (fixForm U) a (−b) = eisForm a b` (`ℤ[ω]`, the `ω ↔ −ω` orientation),
`formEval (fixForm S) = a²+b²` (`ℤ[i]`, disc `−4`).  The sign of `D = tr²−4`
(`disc_sign_is_line_cusp_curve`) makes "Eisenstein ↦ curve" exact: `D < 0` ⟺ definite
norm ⟺ complex-conjugate fixed points ⟺ an elliptic point of `ℍ` ⟺ a bounded torus.

### The Eisenstein period's arithmetic

The disc-`−3` face carries the Eisenstein period.  Its Epstein zeta
`Σ' 1/(a²+ab+b²)^s = 6 ζ(s) L(s, χ₋₃)` is clean for four `∅`-axiom reasons.

**Character (χ₋₃).**  The form represents only the residues `{0,1}` mod 3, never `2`
(`eisCyc_mod3_ne_two`) — the necessary character condition, the disc-`−3` analog of
two-squares avoiding `3 mod 4`.  The proof first shows the custom `mod3` is a ring
homomorphism (`mod3_add`, `mod3_mul`), then decides the nine residue pairs.

**Local splitting.**  Each prime's Euler factor is its splitting in `ℤ[ω]`, indexed by
`χ₋₃(p) = p mod 3`: split (`7 = 3²−3+1`, `13 = 4²−4+1`), ramified (`N(1−ω) = 3`,
`(1−ω)² = −3ω`, the conductor), inert (`2` not a value).  The values form a multiplicative
monoid by the disc-`−3` Brahmagupta–Fibonacci identity `eisForm_composition`
`(a²−ab+b²)(c²−cd+d²) = E²−EF+F²` (`E = ac−bd`, `F = ad+bc−bd`), the `ℤ[ω]` multiplication
law.  Bundled in `eisenstein_local_splitting`.

**Class number one.**  Why a *single* form?  Because `h(−3) = 1`: the only reduced
positive-definite form of discriminant `−3` is the principal `x²+xy+y²`
(`reduced_disc_neg3_unique`).  A reduced `(a,b,c)` with `|b|≤a≤c` and `4ac = b²+3` satisfies
`4a² ≤ 4ac = b²+3 ≤ a²+3`, forcing `3a²≤3`, `a=1`, then `4c = b²+3` with `|b|≤1` forces
`b=±1`, `c=1` — finite, no reciprocity.

**Euclidean covering radius.**  The ring counterpart of `h(−3)=1` is that `ℤ[ω]` is a PID
because it is norm-Euclidean.  The geometric heart is `covering_bound`: with `4x²≤N²`,
`4y²≤N²` (centered remainders `2|·|≤N`), `8(x²−xy+y²) ≤ 6N²` — covering radius² `≤ 3/4 < 1`,
so the Euclidean remainder always shrinks the norm.  Proved by the sum-of-nonnegatives
identity `6N²−8(x²−xy+y²) = 3(N²−4x²)+3(N²−4y²)+(2x+2y)²`.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `fixForm_disc_eq_traceDisc` | `CrossDetTraceField` | form disc of `fixForm M` = `tr²−4`, ∀ `M` |
| `fixForm_automorph` | `CrossDetTraceField` | monodromy preserves its fixed-point form up to `det` |
| `crossdet_number_field_is_trace_field` | `CrossDetTraceField` | the three faces + the universal identity |
| `disc_sign_is_line_cusp_curve` | `CrossDetTraceField` | sign of `tr²−4` = line/cusp/curve |
| `eisCyc_mod3_ne_two` | `EisensteinFormCharacter` | `a²+ab+b² ≢ 2 (mod 3)` (the χ₋₃ fingerprint) |
| `eisForm_composition` | `EisensteinSplitting` | Brahmagupta multiplicativity of the disc-`−3` form |
| `eisenstein_local_splitting` | `EisensteinSplitting` | split / ramified / inert Euler factors |
| `reduced_disc_neg3_unique` | `EisensteinClassNumber` | `h(−3) = 1`: the only reduced form is `x²+xy+y²` |
| `covering_bound` | `EisensteinEuclidean` | covering radius² `≤ 3/4 < 1`: `ℤ[ω]` is Euclidean |

## Research-note provenance

The cross-determinant / Eisenstein frontier note under `research-notes/frontiers/` — the
seed conjecture, the full analysis, and the open frontier below.

## Open frontier

Live in the frontier note under `research-notes/frontiers/`:

  - **The split converse** — *every* `p ≡ 1 (mod 3)` is a value of `a²+ab+b²`, not just the
    recorded witnesses.  Needs the quadratic-residue input (`−3` is a QR mod `p` iff
    `p ≡ 1 mod 3`, i.e. an order-3 element of `(ℤ/p)ˣ` — the primitive-root theorem) plus the
    full Euclidean descent assembled from `covering_bound` (centered division, `gcd`, unique
    factorization).

  - **The period value** — the transcendental `Γ(1/3)`-constant itself.  Not reached from
    inside the `ℕ`/`ℤ` reflection provers: the cubic AGM's geometric-mean step
    `∛(b·(a²+ab+b²)/3)` carries the disc-`−3` form but a cube root, and the analytic value
    `L(1, χ₋₃) = π/√27` needs the `L`-series limit.

## How to verify

```bash
cd lean && lake build E213
python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Real213.CrossDetTraceField
python3 tools/scan_axioms.py E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter
python3 tools/scan_axioms.py E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitting
python3 tools/scan_axioms.py E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinClassNumber
python3 tools/scan_axioms.py E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinEuclidean
```
