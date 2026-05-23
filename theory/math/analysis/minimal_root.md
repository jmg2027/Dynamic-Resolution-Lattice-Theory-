# Minimal Root — Trajectory-as-Witness IVT

**Status**: Closed (`MinimalRootLens` skeleton + monotone refinement
+ unit oracles + signed-left collapse).

## Overview

The **Intermediate Value Theorem in 213 is not an existential claim
but a typed protocol** — `ConsistentOracle` — whose readout *is*
the root cut.

> *"Minimal root" emerges deterministically from the lens's choice
> rule (always-prefer-left), not from any external decidability
> hypothesis.*

This is G2 (trajectory-as-object) applied to bisection: the
locatedness assumption that haunts Bishop-style IVT is replaced by
a **structural type-level commitment from the oracle**.

The single citable Lean definition is `MinimalRootLens ∈
Analysis/DyadicSearch/MinimalRootLens.lean`.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Analysis/DyadicSearch/` (9 files)
- **Umbrella**: imports via `Analysis/DyadicSearch.lean`
- **∅-axiom status**: PURE on structural skeleton

### Sub-cluster organization

| Sub-cluster | Files | Purpose |
|---|---|---|
| **Core mechanics** | `DyadicBracket`, `DyadicTrajectory`, `DyadicRiemann`, `IVT` | Dyadic-bracket type, bisection trajectory, Riemann sum, base IVT |
| **Minimal-root Lens** | `MinimalRootLens`, `MinimalRootLensMonotone` | Trajectory-as-witness + monotone refinement |
| **Oracle + collapse** | `ConsistentOracle`, `UnitConsistentOracles`, `SignedLeftCollapse` | Consistent-oracle predicate, unit-interval oracles, signed-left collapse |

## The narrative

### Why classical IVT fails in 213

Two tempting framings, both rejected:

**(a) ε-δ approximation**: `∀ m k, ∃ c, |f c| < 1/k at precision m`.
Requires sign-decidability at every refinement → forces
`Decidable` instance synthesis → pulls in `propext`.  Not 213-native.

**(b) Isolated-root hypothesis**: add `IsolatedRoot f` predicate,
derive uniqueness, conclude exact `cutEq`.  Imports a classical
assumption that can't be discharged from the Raw axiom set.  Not
213-native.

Both routes treat the bisection sequence as *evidence for* an
existential root.  213's approach is different.

### The 213-native approach: trajectory-as-witness

In 213, the **bisection trajectory itself is the witness**.  No
external decidability needed.  The `ConsistentOracle` type encodes
the choice protocol:

```
ConsistentOracle f := the typed commitment that, at each
                     bisection step, f's sign is consistent across
                     refinements (no flip-flop)
```

Given a `ConsistentOracle`, the `MinimalRootLens` is the
deterministic readout: at each step, take the left half if the
sign-witness allows, else the right.  The infinite trajectory
**is** the root cut — not "converges to" the root, but **is** the
root, as a Real213 `Cut`.

### Why this matters (trajectory-witness IVT's thesis)

> *"편한 길은 213이 아니지"*  — Mingu

The classical IVT formulation imports decidability that 213 doesn't
have natively.  Rather than work around with propext or
locatedness assumptions, 213 reframes the question: instead of
*proving* an existential, *construct* the root deterministically
from a typed protocol.

This pattern generalizes beyond IVT:
- **Bisection search**: deterministic trajectory
- **Optimization**: deterministic descent
- **Fixed-point computation**: deterministic iteration

Each is a `Lens` application whose output is what classical
mathematics would phrase existentially.

### Connection to DRLT physics

Physics observables that classical analysis would phrase as
"there exists a value satisfying...  " can be reframed in 213
as `ConsistentOracle` + `Lens` constructions:
- α_em(IR) = output of a `ConsistentOracle` on the cup-ring
  precision sequence
- Atomic mass identifications = `MinimalRootLens` readouts on
  appropriate Real213 cuts

`Lib/Physics/AtomicBase/Capstone` uses the DyadicSearch IVT
machinery directly.

## Key results

| Theorem / Def | Module | Statement |
|---|---|---|
| `DyadicBracket` | `DyadicBracket` | Type of dyadic bracket sequences |
| `DyadicTrajectory` | `DyadicTrajectory` | Bisection trajectory in Real213 |
| `ConsistentOracle f` | `ConsistentOracle` | Typed sign-consistency protocol |
| `MinimalRootLens` | `MinimalRootLens` | Trajectory-as-witness Lens |
| `MinimalRootLensMonotone` | `MinimalRootLensMonotone` | Monotone refinement |
| `unit_consistent_oracle` | `UnitConsistentOracles` | Unit-interval instances |
| `signedLeftCollapse` | `SignedLeftCollapse` | Always-prefer-left collapse |
| Base IVT | `IVT` | Classical statement in 213-native form |

## Multi-variate bisection — closed (MultiVarBisection.lean)

`Lib/Math/Analysis/DyadicSearch/MultiVarBisection.lean` (10 PURE)
lifts the single-variate trajectory-witness IVT to **simultaneous
root finding on n variables**:

  · `MultiBracket n := Fin n → DyadicBracket` — n-tuple of brackets.
  · `MultiConsistentOracle n mb` — per-coordinate consistent oracles.
  · `MultiCauchyCutSeq n := Fin n → CauchyCutSeq` — the joint readout.
  · `MultiConsistentOracle.toMultiCauchy` — n-tuple of Cauchy readouts.
  · `unitMultiBracket n`, `unitMultiConsistentOracle n`,
    `unitMultiCauchy n` — canonical unit n-bracket instance.
  · Smoke at n = 2 (planar), n = 3 (spatial), n = 5 (atomic
    dimension `d = 5`).
  · ★★★★ `multi_var_capstone` — bundles existence, projection,
    and per-coordinate equality.

213-native reading: the multi-variate IVT is a **product** of
single-variate IVTs.  No extra structural machinery needed — n
independent `ConsistentOracle`s compose to a single product oracle,
yielding n independent CauchyCutSeqs.

## Full RootCertificate packaging — closed (RootCertificate.lean, 9 PURE)

`Lib/Math/Analysis/DyadicSearch/RootCertificate.lean` packages the
trajectory-witness IVT readout into a single structure:

  `RootCertificate f` bundles `bracket : DyadicBracket` plus the
  `BracketSignChange f bracket` witness (sign change at unit
  precision over the bracket endpoints).

  · `RootCertificate.ofBracket` — promote any `BracketSignChange`
    to a certificate.
  · `RootCertificate.refine` — apply one `bisectStep` under
    `signedLeftOracle f`, preserving the certificate via
    `bisectStep_signed_left_preserves_sign_change`.
  · `RootCertificate.refineN` — refine N steps.
  · `lowerCut` / `upperCut` — endpoint accessors.
  · `signLeft` / `signRight` — sign witnesses (`f.lowerCut 0 1 =
    false`, `f.upperCut 0 1 = true`).
  · ★★★★★ `root_certificate_capstone` packages existence,
    bracket access, and both sign witnesses.

Reading: the IVT root of `f` is a typed certificate carrying
bracket endpoints + sign witnesses, refined under
`signedLeftOracle`-bisection.  No `∃` existential, no `Decidable`
on the root — just constructive Nat-decidable data.

## Open frontier

`MinimalRootLens` skeleton is closed.  Open extensions:

1. ~~**Full root-certificate**~~ — CLOSED via
   `RootCertificate.lean` (9 PURE) above.  Bundles bracket + sign
   change + refine combinators.

2. ~~**Generalization to multi-variate**~~ — CLOSED via
   `MultiVarBisection.lean` (10 PURE).

3. ~~**Continuity-without-ε** alternative~~ — CLOSED via
   `Real213/OracleContinuity.lean` (companion chapter).

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Analysis.DyadicSearch
python3 tools/scan_axioms.py Lib/Math/Analysis/DyadicSearch
```

## Citation guidance

- ✅ `theory/math/analysis/minimal_root.md` (narrative)
- ✅ archived note: `research-notes/archive/minimal_root/G31_*.md`
