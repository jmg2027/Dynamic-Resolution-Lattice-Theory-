# lean/E213/ — formal source of truth

The authoritative state of 213.  All other documents (guide/, books/,
papers/, research-notes/, blueprints/) are entry points INTO this
body of work or derived artifacts.

> **Theoretical architecture** is canonically documented in
> `ARCHITECTURE.md` (this directory).  That file defines what each
> layer IS, the dependency graph, naming conventions, and open
> questions.  This INDEX.md is a *navigation* document; for *theory*,
> read ARCHITECTURE.md first.

## Layered architecture

```
Kernel/      ★ deep-embedded 213 kernel (literally 0 axiom)
  ↓
Firmware/    Raw axiom (a, b, slash, slash_comm)
             + Atomicity/ (forced shape uniqueness — d=5, (NS,NT)=(3,2)
                            proven from outside, no Raw import)
  ↓
Hypervisor/  Lens framework + Lens/{Instances, Characterisation}/
  ↓
Meta/        true metatheory: UniversalLens family, SelfRecognising
             (R1-R4 hierarchy), BitPatternUniqueness, RawInductionDemo
  ↓
Math/        formalized math (Cohomology, Linalg, Pigeonhole)
Physics/     formalized physics (267 files, 18 sub-clusters)
Research/    exploratory + Real213 marathon (332 files, 17 sub-clusters)
```

See `ARCHITECTURE.md` (this directory) for canonical theoretical
definitions of each layer.

## Layer roles

| Layer | Purpose | Axiom load |
|---|---|---|
| Kernel/ | 14 files, 101 theorems literally 0 axiom (Lean-side scaffolding for 213) | none |
| Firmware/ | Raw axiom (4-clause) + `Atomicity/` sub-cluster (forced shape uniqueness — d=5, (NS,NT)=(3,2) proven from outside, not derived from Raw) | none |
| Hypervisor/ | Lens framework (catamorphism Raw → α) | none |
| Meta/ | Lens metatheory (Universal Lens variants, R4Codomain, ...) | mostly none |
| Math/ | Cohomology, Linalg, Pigeonhole + horizontal math frameworks | mixed |
| Physics/ | 213 physics formalization (App-layer derivations) | mixed |
| Research/ | Real213 marathon, dyadic predictors, exploratory | mixed |
| Infinity/ | limit/compactification (mostly external bridges) | mixed |
| Tactic/ | custom tactics (Omega213, VerifyR4, ...) | none |
| App/ | applications | none |

> **Architectural note (2026-05-XX)**: the previous `OS/` directory
> was a misnomer.  Its 7 atomicity-shape proofs were independent ℕ-
> arithmetic theorems (no Raw import) that *predict* the Raw axiom's
> shape — they belong inside Firmware as the axiom's forced-uniqueness
> proof obligation, NOT as a separate "OS layer" between Firmware
> and Hypervisor.  See `Firmware/Atomicity/README.md` for theory.
> The general-purpose `Pigeonhole.lean` (universal Fin infrastructure,
> atomicity-agnostic) moved to `Math/Pigeonhole.lean`.

## Capstone navigation

Detailed theorem index: `CAPSTONE_INDEX.md` (root)
Strict-zero-axiom list: `STRICT_ZERO_AXIOM.md` (root)

Top achievements:
  - `Physics/ValidationStandardOne.validation_standard_capstone`
  - `Physics/PureAtomicObservables.pure_atomic_observables_capstone`
  - `Physics/AlphaEMMasterCapstone.alpha_em_master_capstone`
  - `Physics/AlphaEMMilestone.alpha_em_milestone`
    (CLAUDE.md "first milestone of rewriting physics from scratch")

## Where to read what

| Question | Where to look |
|---|---|
| "What does DRLT compute?" | `Physics/Capstones/PureAtomicObservables.lean` + `CAPSTONE_INDEX.md` |
| "How does α_em derive?" | `Physics/AlphaEM/` chain (18 files) |
| "Where is N_universe?" | `Physics/Foundations/NUniverseFractalDepth.lean` |
| "Why finite N only?" | `Research/Real213/DyadicTrajectory.lean` (limit ≠ exact) + `LESSONS_LEARNED.md` 교훈 1 |
| "What are the atomic primitives?" | `Firmware/Atomicity/Five.lean` + `Firmware/Atomicity/PairForcing.lean` |
| "How is the kernel 0-axiom?" | `Kernel/` 14 files + `tools/kernel_regress.sh` |
| "Cohomology classes?" | `Math/Cohomology/` (175 files in 10 sub-clusters) + `rust-engine/docs/cohomology-classes.md` |
| "Lens framework?" | `Hypervisor/Lens.lean` + `Hypervisor/Lens/{Instances,Characterisation}/` + `Meta/UniversalLens/` |
| "Theoretical architecture?" | `ARCHITECTURE.md` (this directory) |

## Build

```
cd lean && lake build           # full lib build
lake env lean E213/Foo.lean     # ad-hoc check
lake env lean -e '...'           # eval (used by lean-rust-diff)
```

## Tooling

  - `Tactic/Omega213.lean` — axiom-free Nat arithmetic (drop-in for omega)
  - `Tactic/VerifyR4.lean` — R4Codomain instance diagnostic
  - `Tools/CertChecker.lean` — Lean-side certificate verifier

## Cleanup status (2026-05-01, post Phase 3+7+Research-reorg)

Lean tree count: ~810 files (unchanged in count; reorganized in
structure).

Sub-clustered (across all sessions):
  - `Math/Cohomology/Dyadic/` — 8 sub-clusters (ArithFSM, BitFSM,
    Pell, Fib, Trib, Legendre, Pisano, Archive)
  - `Math/Cohomology/{Bipartite, Cochain, Cup, CupAW, Delta,
    Fractal, Hodge, Universal}/` — 8 sub-clusters
  - `Research/Real213/` — 180 files (Bishop analysis marathon)
  - `Research/CayleyDickson/` — 29 files (Cayley-Dickson tower)
  - `Research/{Lens, Cauchy, ModArith, Kernel, Instance, Morphism,
    Irrational, Universal, Leaves, Modulus, Choice, Diagonal, Raw,
    Hyper, Refines}/` — 15 sub-clusters (114 of 127 flat files
    moved 2026-05-01); 13 misc files retained at root.  See
    `Research/INDEX.md`.

Pending:
  - Phase 1 versioning consolidation (PisanoPredictor 9→1) —
    determined N/A (chain is each-adds-new-primes, not redundant)
  - Phase 5 omega migration: 343 → 223 calls (-35%); diminishing
    returns reached
  - Native213 deeper: Nat.div_* avoidance via `q*n + r = x ∧ r < n`
    decomposition

Hands-off layers (well-organized): Kernel, Firmware (with
Atomicity/), Hypervisor (with Lens/{Instances,Characterisation}/),
App, Meta, Tactic, Tools, Infinity.

Architecture audits (completed 2026-05-XX):
  - OS/ dissolved (was a misnomer) — atomicity proofs migrated to
    Firmware/Atomicity/, Pigeonhole to Math/Pigeonhole.lean
  - Phase{2,3,4} retired — Substrate/, AtomicCorrespondences/,
    distributed across topical clusters
  - Phase4/Library kept as 27 separate per-topic stubs (the earlier
    27→6 merge was reverted as bad-for-modularity)
  - Meta/Lens concrete instances → Hypervisor/Lens/Instances/;
    characterisations → Hypervisor/Lens/Characterisation/
  - namespace ↔ path alignment via tools/sync_namespaces.py
  - `Math/Cohomology/` 19 flat-root utility files — small enough
    they might fold into existing sub-clusters or stay at root

## Branches

  - `main` — base
  - `claude/213-rust-engine-SloKB` — current head (rust-engine + merged math)
  - `claude/review-paper-directory-nDw9L` — math-track parallel
