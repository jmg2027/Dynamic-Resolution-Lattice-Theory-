# `Analysis/DyadicSearch/` — dyadic-search IVT machinery

Dyadic-bracket Intermediate Value Theorem on Real213 cuts.  Includes
G31 trajectory-as-witness `MinimalRootLens` (Layer 3c morphism-
collapse closure) — connects to DRLT physics observables.

## Files (9)

### Core mechanics (4)
  - `DyadicBracket.lean`        — DyadicBracket type
  - `DyadicTrajectory.lean`     — trajectory under bisection
  - `DyadicRiemann.lean`        — Riemann-sum form on dyadic
  - `IVT.lean`                  — base Intermediate Value Theorem

### Minimal-root Lens (G31, 2)
  - `MinimalRootLens.lean`            — `MinimalRootLens`
                                         (trajectory-as-witness)
  - `MinimalRootLensMonotone.lean`    — monotone refinement

### Oracle + collapse (3)
  - `ConsistentOracle.lean`        — consistent-oracle predicate
  - `UnitConsistentOracles.lean`   — unit-interval oracles
  - `SignedLeftCollapse.lean`      — signed-left collapse

## Where to add new files

  - New IVT variant             → `IVT*` / `<seq>IVT.lean`
  - Trajectory / witness        → `<...>Trajectory` /
                                  `<...>RootLens`
  - Oracle / collapse           → `<...>Oracle` / `<...>Collapse`

## Connection

  - `Lib/Physics/AtomicBase/Capstone` — uses DyadicSearch IVT
  - `research-notes/G31` — trajectory-as-witness framework
