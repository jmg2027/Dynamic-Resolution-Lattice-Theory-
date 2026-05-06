# lean/E213/ — formal source of truth

The authoritative state of 213.  All other documents (guide/, books/,
papers/, research-notes/, blueprints/) are entry points INTO this
body of work or derived artifacts.

> **Theoretical architecture** is canonically documented in
> `ARCHITECTURE.md` (this directory).  That file defines what each
> layer IS, the dependency graph, naming conventions, and open
> questions.  This INDEX.md is a *navigation* document; for *theory*,
> read ARCHITECTURE.md first.

## Layered architecture (post-2026-05-XX deep reorg)

ONE vertical axis (Kernel → App), Math/ and Physics/ as topical
roots whose individual files each live at one of the vertical
layers (computed by `tools/layer_audit.py` from import closure).

```
Kernel/      ★ 24 files, 0-axiom scaffolding
             + Tactic/ (Nat213, Mod213, Fin213, Pow213,
                        Omega213, QuadNorm + Test)
  ↓
Firmware/    27 files: Raw axiom (a, b, slash, slash_comm)
             + Atomicity/ (forced d=5, (NS,NT)=(3,2))
             + Tools/CertChecker
  ↓
Hypervisor/  101 files: Lens framework
             Lens.lean umbrella + 12 sub-cluster umbrellas
             (Instances/, Characterisation/, Lattice/, Compose/,
              Properties/, Morphism/, Leaves/, Refines/, Kernel/,
              Universal/, AxiomLenses/{Bridges, Core}/) +
             Initiality.lean + SemanticAtom.lean
  ↓
Meta/        30 files: UniversalLens / Universal / Tactic
             sub-cluster umbrellas + SelfRecognising codomain
             hierarchy (CommBinary/NonVanishing/Conjugation),
             AxiomMinimality{,Capstone}, BitPatternUniqueness,
             RawInductionDemo, CUniquenessBridge
  ↓
App/         1 file (Simplex)
OS/          14 files: HodgeConjecture/Bridges/ +
             Physics/Capstones/ (motivic-cohomology + physics
             integration capstones)

Math/        491 files (topical): Cohomology/, Real213/, Analysis/,
             CayleyDickson/, Cauchy/, ModArith/, Modulus/, Diagonal/,
             Irrational/, Hyper/, Choice/, Infinity/, Linalg213/,
             AxiomSystems/, Polynomial213/, Trajectory/, Tactic/
             (HurwitzRing, IntSquare, QuadExtension)
Physics/     128 files (topical): AlphaEM, Couplings, Hadron, Higgs,
             Mass, Mixing, Nuclear, Cosmology, Atomic, Simplex,
             Basel, YangMills, Substrate, Foundations
```

See `ARCHITECTURE.md` (this directory) for canonical theoretical
definitions of each layer + the per-file layer-derivation rule.

## Layer roles

| Layer | Purpose | Axiom load |
|---|---|---|
| Kernel/ | 24 files, 0-axiom scaffolding + Tactic/ (Nat213, Mod213, Fin213, Pow213, Omega213, QuadNorm) | none |
| Firmware/ | 27 files: Raw axiom (4-clause) + Atomicity/ + Tools/CertChecker | none |
| Hypervisor/ | 101 files: Lens framework (umbrella + 12 sub-clusters) | none |
| Meta/ | 30 files: metatheorems + Tactic/ + UniversalLens/ | mostly none |
| App/ | 1 file (Simplex) | none |
| OS/ | 14 files: top-level integration capstones (HodgeConjecture/Bridges, Physics/Capstones) | mostly none |
| Math/ | 491 files topical math (Cohomology, Real213, …); each file at its natural vertical layer | mixed |
| Physics/ | 128 files topical physics; each file at its natural vertical layer | mixed |

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
| "Why finite N only?" | `Math/Real213/DyadicTrajectory.lean` (limit ≠ exact) + `LESSONS_LEARNED.md` |
| "What are the atomic primitives?" | `Firmware/Atomicity/Five.lean` + `Firmware/Atomicity/PairForcing.lean` |
| "How is the kernel 0-axiom?" | `Kernel/` 18 files + `tools/kernel_regress.sh` |
| "Cohomology classes?" | `Math/Cohomology/` (~217 files in 10 sub-clusters) + `rust-engine/docs/cohomology-classes.md` |
| "Lens framework?" | `Hypervisor/Lens.lean` + 12 sub-cluster umbrellas under `Hypervisor/Lens/` + `Meta/UniversalLens/` |
| "Theoretical architecture?" | `ARCHITECTURE.md` (this directory) |

## Build

```
cd lean && lake build           # full lib build
lake env lean E213/Foo.lean     # ad-hoc check
lake env lean -e '...'           # eval (used by lean-rust-diff)
```

## Tooling

  - `Kernel/Tactic/Omega213.lean` — axiom-free Nat arithmetic
    (drop-in for omega; macro lives in `namespace E213.Tactic`
    short-form for ergonomic `open E213.Tactic`)
  - `Meta/Tactic/VerifyConjugation.lean` — `ConjugationCodomain`
    instance diagnostic (`#verify_conjugation MyType`)
  - `Firmware/Tools/CertChecker.lean` — Lean-side certificate verifier
  - `tools/layer_audit.py` (repo root) — derive each file's natural
    vertical layer from import closure; reports violations + topical
    cluster depth

## Cleanup status (2026-05-XX, post-M11/M12 umbrella sweep)

Lean tree: ~825 files (post-reorg + 38+ new sub-cluster umbrellas
in M11/M12).  Every directory now has a `<DirName>.lean` umbrella
(R2 / R7 of `research-notes/CONSOLIDATION_PROTOCOL.md`).

Distribution (per `tools/layer_audit.py`):

| top-folder | Kernel | Firmware | Hypervisor | Meta | App | total |
|---|---|---|---|---|---|---|
| Kernel/      | 23 |   0 |   0 |  0 | 0 |  24 |
| Firmware/    |  0 |  27 |   0 |  0 | 0 |  27 |
| Hypervisor/  |  0 |   0 |  89 |  0 | 0 | 101 |
| Meta/        |  0 |   0 |   0 | 27 | 0 |  30 |
| App/         |  0 |   0 |   0 |  0 | 1 |   1 |
| OS/          |  0 |  11 |   1 |  0 | 0 |  14 |
| Math/        | 49 | 235 | 176 |  9 | 0 | 491 |
| Physics/     |  0 | 116 |  11 |  0 | 0 | 128 |

(Counts are total files including the new `<DirName>.lean`
sub-cluster umbrellas.)

Architecture audits (completed 2026-05-XX):
  - OS/ dissolved → Firmware/Atomicity/ + Math/Pigeonhole
  - Phase{2,3,4} retired → distributed across Physics/ topical clusters
  - Research/ marker eliminated → Math/Real213/, Math/CayleyDickson/,
    Math/Cauchy/, Hypervisor/Lens/{Lattice,Compose,Properties,…}/,
    Meta/{AxiomMinimality,Universal/}, Firmware/Raw/{DecEq, …}
  - Infinity/ → Math/Infinity/
  - Tactic/ distributed by import-derived layer (Kernel, Math, Meta)
  - Tools/ → Firmware/Tools/
  - namespace ↔ path alignment via `tools/sync_namespaces.py`
  - Layer audit zero-violations enforced via `tools/layer_audit.py`

## Branches

  - `main` — base
  - `claude/213-rust-engine-SloKB` — current head (rust-engine + merged math)
  - `claude/review-paper-directory-nDw9L` — math-track parallel
