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
Kernel/      ★ 18 files, 101 theorems literally 0-axiom
             + Tactic/Omega213, QuadNorm
  ↓
Firmware/    Raw axiom (a, b, slash, slash_comm)
             + Atomicity/ (forced d=5, (NS,NT)=(3,2))
             + Tools/CertChecker
  ↓
Hypervisor/  Lens framework (78 files):
             Lens.lean umbrella + Lens/{Instances, Characterisation,
             Lattice, Compose, Properties, Morphism, Leaves, Refines,
             Kernel, Universal}/ + Initiality.lean + SemanticAtom.lean
  ↓
Meta/        true metatheory (23 files): UniversalLens family,
             SelfRecognising R1-R4, AxiomMinimality{,Capstone},
             BitPatternUniqueness, RawInductionDemo,
             CUniquenessBridge + Tactic/{VerifyR4, DeriveR4Codomain}
  ↓
App/         applications (Simplex)

Math/        484 files (topical): Cohomology/, Linalg213/, Real213/,
             CayleyDickson/, Cauchy/, ModArith/, Modulus/, Diagonal/,
             Irrational/, Hyper/, Choice/, Infinity/, Tactic/
             (HurwitzRing, IntSquare, QuadExtension), Pigeonhole, …
Physics/     275 files (topical): AlphaEM, Couplings, Hadron, Higgs,
             Mass, Mixing, Nuclear, Cosmology, Atomic, Simplex,
             Basel, FamousCoincidences, YangMills, Capstones,
             Library, Substrate, AtomicCorrespondences, Foundations
```

See `ARCHITECTURE.md` (this directory) for canonical theoretical
definitions of each layer + the per-file layer-derivation rule.

## Layer roles

| Layer | Purpose | Axiom load |
|---|---|---|
| Kernel/ | 18 files, 101 thms literally 0 axiom (scaffolding + Tactic/Omega213, QuadNorm) | none |
| Firmware/ | Raw axiom (4-clause) + Atomicity/ + Tools/CertChecker | none |
| Hypervisor/ | Lens framework (78 files: framework + 9 sub-clusters) | none |
| Meta/ | metatheorems + Tactic/{VerifyR4, DeriveR4Codomain} | mostly none |
| App/ | applications (Simplex) | none |
| Math/ | 484 files topical math (Cohomology, Real213, …); each file at its natural vertical layer | mixed |
| Physics/ | 275 files topical physics; each file at its natural vertical layer | mixed |

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
| "Cohomology classes?" | `Math/Cohomology/` (~190 files in 10 sub-clusters) + `rust-engine/docs/cohomology-classes.md` |
| "Lens framework?" | `Hypervisor/Lens.lean` + `Hypervisor/Lens/{Instances,Characterisation,Lattice,Compose,Properties,Morphism,Leaves,Refines,Kernel,Universal}/` + `Meta/UniversalLens/` |
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
  - `Meta/Tactic/VerifyR4.lean` — R4Codomain instance diagnostic
  - `Firmware/Tools/CertChecker.lean` — Lean-side certificate verifier
  - `tools/layer_audit.py` (repo root) — derive each file's natural
    vertical layer from import closure; reports violations + topical
    cluster depth

## Cleanup status (2026-05-XX, post deep reorg)

Lean tree: 907 files.  Top-level `Research/`, `Infinity/`, `Tactic/`,
`Tools/` retired and fully distributed by content into Math/Physics +
the vertical layers.  Math/ and Physics/ are the only topical roots.

Distribution (per `tools/layer_audit.py`):

| top-folder | Kernel | Firmware | Hypervisor | Meta | App | total |
|---|---|---|---|---|---|---|
| Kernel/      | 18 |   0 |   0 |  0 | 0 | 18  |
| Firmware/    |  0 |  25 |   0 |  0 | 0 | 25  |
| Hypervisor/  |  0 |   0 |  78 |  0 | 0 | 78  |
| Meta/        |  0 |   0 |   0 | 23 | 0 | 23  |
| App/         |  0 |   0 |   0 |  0 | 1 |  1  |
| Math/        | 36 | 211 | 231 |  6 | 0 | 484 |
| Physics/     |  2 | 168 | 105 |  0 | 0 | 275 |

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
