# lean/E213/ — formal source of truth

The authoritative state of 213.  All other documents (guide/, books/,
papers/, research-notes/, blueprints/) are entry points INTO this
body of work or derived artifacts.

## Layered architecture

```
Kernel/      ★ deep-embedded 213 kernel (literally 0 axiom)
  ↓
Firmware/    Raw axiom layer (a, b, slash, slash_comm)
  ↓
OS/          Atomicity (d=5) + canonical structures (PairForcing → NS=3, NT=2)
  ↓
Hypervisor/  Lens framework (cross-layer bridge)
  ↓
Meta/        Universal Lens, AxiomMinimality, R4Codomain hierarchy
  ↓
Math/        formalized math (Cohomology, Linalg)
Physics/     formalized physics (267 files)
Research/    exploratory + Real213 marathon (332 files)
```

## Layer roles

| Layer | Purpose | Axiom load |
|---|---|---|
| Kernel/ | 14 files, 101 theorems literally 0 axiom | none |
| Firmware/ | Raw type with 4 definitional commitments | none |
| OS/ | atomicity (d=5) + (NS,NT)=(3,2) derived | none |
| Hypervisor/ | Lens framework (Lens, R4Codomain) | none |
| Meta/ | Universal Lens, kernel meta-theory | mostly none |
| Math/ | Cohomology, Linalg | mixed |
| Physics/ | 213 physics formalization | mixed |
| Research/ | Real213 marathon, dyadic predictors, exploratory | mixed |
| Infinity/ | limit/compactification (mostly external bridges) | mixed |
| Tactic/ | custom tactics (Omega213, VerifyR4, ...) | none |
| App/ | applications | none |

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
| "What does DRLT compute?" | `Physics/PureAtomicObservables.lean` + `CAPSTONE_INDEX.md` |
| "How does α_em derive?" | `Physics/AlphaEM*.lean` chain (5 files) |
| "Where is N_universe?" | `Physics/NUniverseFractalDepth.lean` |
| "Why finite N only?" | `Research/Real213DyadicTrajectory.lean` (limit ≠ exact) + `LESSONS_LEARNED.md` 교훈 1 |
| "What are the atomic primitives?" | `OS/Atomicity.lean` + `OS/PairForcing.lean` |
| "How is the kernel 0-axiom?" | `Kernel/` 14 files + `tools/kernel_regress.sh` |
| "Cohomology classes?" | `Math/Cohomology/` (147 files) + `rust-engine/docs/cohomology-classes.md` |
| "Lens framework?" | `Hypervisor/` + `Meta/UniversalLens*.lean` |

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

## Cleanup status (per AUDIT_GUIDE.md)

Lean tree count: ~810 files.  Cleanup targets:
  - `Math/Cohomology/Dyadic*` — 77 flat files → sub-cluster reorg pending
  - `Research/` — 332 files → dependency-graph audit pending
  - omega → omega213 migration: 195 calls / 50 files pending

Hands-off layers (well-organized): Kernel, Firmware, OS, Hypervisor,
App, Meta, Physics.

## Branches

  - `main` — base
  - `claude/213-rust-engine-SloKB` — current head (rust-engine + merged math)
  - `claude/review-paper-directory-nDw9L` — math-track parallel
