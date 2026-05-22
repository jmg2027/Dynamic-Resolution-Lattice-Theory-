# Minimal Root — Trajectory-as-Witness IVT

**Status**: Closed (`MinimalRootLens` skeleton + monotone refinement
+ unit oracles + signed-left collapse).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 (multi-note absorption).  G31 → 1 chapter; archived.

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
| **Minimal-root Lens (G31)** | `MinimalRootLens`, `MinimalRootLensMonotone` | Trajectory-as-witness + monotone refinement |
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

### Why this matters (G31's thesis)

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

## Research-note provenance

One note (`G31`) — archived to
`research-notes/archive/minimal_root/`:

| Note | Theme |
|---|---|
| `G31_minimal_root_lens.md` | Trajectory-as-witness IVT — typed protocol replaces existential |

## Open frontier

`MinimalRootLens` skeleton is closed.  Open extensions:

1. **Full root-certificate** (lower / upper / zero): the current
   skeleton gives the cut; a full `RootCertificate` packaging
   (lower bound, upper bound, witness of vanishing) awaits the
   **monotone-polynomial milestone** (next).

2. **Generalization to multi-variate**: bisection on `Cut^n` for
   simultaneous root-finding.  Currently single-variable only.

3. **Continuity-without-ε** alternative: phrase the continuity
   assumption itself as a `ConsistentOracle` extension, eliminating
   the implicit ε-δ residue in the current definition.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Analysis.DyadicSearch
python3 tools/scan_axioms.py Lib/Math/Analysis/DyadicSearch
```

## Citation guidance

- ✅ `theory/math/analysis/minimal_root.md` (narrative)
- ✅ archived note: `research-notes/archive/minimal_root/G31_*.md`
