# lean/E213/ — formal source of truth

The authoritative state of 213.  All other documents (guide/, books/,
papers/, research-notes/, blueprints/) are entry points INTO this
body of work or derived artifacts.

> **Theoretical architecture** is canonically documented in
> `ARCHITECTURE.md` (this directory).  That file defines what each
> layer IS, the dependency graph, naming conventions, and open
> questions.  This INDEX.md is a *navigation* document; for *theory*,
> read ARCHITECTURE.md first.

## Layered architecture (4 ring + Meta, 2026-05-12 spec)

213 is a **4-ring** hierarchy (Term → Theory → Lens → Lib) plus
**Meta** as a ring-independent Lean 4 bridge.  Each ring imports
only from the immediately-below ring's `API.lean` (and from Meta).
See `ARCHITECTURE.md` (this directory) for the canonical spec.

```
Term/     ★ 12 files — Raw 의 구현체 (deep-embedded Tree
            substrate, Bool comparators, Sound bridges, Pair/Rat,
            Decide, Demo, MonomialAxioms).  ★ literally 0-axiom.
  ↓
Theory/   41 files — 213 axiom 자체 (Raw + 4-clause commitments)
            + Atomicity (forced d=5, (NS,NT)=(3,2))
            + Closed (Bool213, Nat213, RawCut, NumberingSystem)
            + Nat213/Tower/CDDouble/RawCmpIndependence.
  ↓
Lens/    121 files — Lens framework (catamorphism Raw → α).
            Algebra/ AxiomLenses/ Cardinality/ Compose/
            Instances/ Lattice/ Properties/ Universal/ Internal/
            sub-clusters + Initiality + SemanticAtom + EqPW.
  ↓
Lib/Math/    743 files (43 sub-clusters): CayleyDickson, Real213,
             SignedCut, Probability, Cohomology, DyadicFSM,
             HodgeConjecture, Analysis, Linalg213, Cauchy,
             ModArith, Modulus, Irrational, Polynomial213,
             Trajectory, …
Lib/Physics/ 165 files (17 sub-clusters): AlphaEM, Couplings,
             Hadron, Higgs, Mass, Mixing, Nuclear, Cosmology,
             Atomic, Simplex, Basel, YangMills, Capstones,
             Substrate, Foundations, Certificates, …

Meta/    37 files (ring-independent) — Lean 4 bridge.
             SelfRecognising (CommBinary/NonVanishing/Conjugation
             Codomain typeclass tower), AxiomMinimality{,Capstone},
             LensInternality, BitPatternUniqueness, Tactic/
             (Nat213, Mod213, Fin213, Pow213, Omega213, QuadNorm,
              NativeGuard, PureGuard, VerifyConjugation,
              DeriveConjugationCodomain), Nat/Int213/Algebra213
             helpers.  Any ring may import from Meta.
```

## Layer roles

| Layer | Files | Role | Axiom load |
|---|---|---|---|
| Term/      | 12  | Raw 의 구현체 (Tree, Term, comparators)  | ★ 0  |
| Theory/    | 41  | Raw axiom + Atomicity + Closed types     | mostly 0 |
| Lens/      | 121 | Lens framework + sub-clusters            | mostly 0 |
| Lib/Math/  | 743 | 213-native mathematics (43 sub-clusters) | mixed |
| Lib/Physics/| 165| 213-native physics (17 sub-clusters)     | mixed |
| Meta/      | 37  | Lean 4 bridge (tactics + typeclasses)    | mostly 0 |

Total: 1127 .lean files.

> **Architectural history**: Pre-2026-05-12 layers were named
> Kernel/Firmware/Hypervisor (OS-metaphor) and there was an
> orchestration ring `OS/`; both renamings + the OS/ dissolution
> are in `git log`.  Pre-2026-05-13 `App/` directory was also
> dissolved (its sole file `App/Simplex.lean` moved to
> `Lib/Math/Combinatorics/Simplex5.lean`).  Current spec is in
> `ARCHITECTURE.md`.

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
| "What does DRLT compute?"     | `Lib/Physics/Capstones/PureAtomicObservables.lean` + `CAPSTONE_INDEX.md` |
| "How does α_em derive?"       | `Lib/Physics/AlphaEM/` chain |
| "Where is N_universe?"        | `Lib/Physics/Foundations/NUniverseFractalDepth.lean` |
| "Why finite N only?"          | `Lib/Math/Real213/Bisection/DyadicTrajectory.lean` (limit ≠ exact) + `LESSONS_LEARNED.md` |
| "What are the atomic primitives?" | `Theory/Atomicity/Five.lean` + `Theory/Atomicity/PairForcing.lean` |
| "How is Term ring 0-axiom?"   | `Term/` 12 files + `tools/kernel_regress.sh` + `STRICT_ZERO_AXIOM.md` |
| "Cohomology classes?"         | `Lib/Math/Cohomology/` (94 files in 11 sub-clusters) + `rust-engine/docs/cohomology-classes.md` |
| "Lens framework?"             | `Lens/LensCore.lean` + 9 sub-cluster umbrellas under `Lens/` + `Lens/Universal/Witnesses/` |
| "Universal-Lens witnesses?"   | `Lens/Universal/Witnesses/` (moved from Meta 2026-05-13) |
| "Raw-native number types?"    | `Theory/Closed/Nat213.lean` + `Theory/Nat213/Core.lean` + `Theory/Tower/{NatPairToInt,NatPairToQPos,NatTripleToZ2}.lean` |
| "Theoretical architecture?"   | `ARCHITECTURE.md` (this directory) |

## Build

```
cd lean && lake build           # full lib build
lake env lean E213/Foo.lean     # ad-hoc check
lake env lean -e '...'           # eval (used by lean-rust-diff)
```

## Tooling

  - `Meta/Tactic/Omega213.lean` — axiom-free Nat arithmetic
    (drop-in for omega; macro lives in `namespace E213.Tactic`,
    short-form for ergonomic `open E213.Tactic`).
    Moved from Term/Tactic/ 2026-05-12 (ring-independent → Meta).
  - `Meta/Tactic/VerifyConjugation.lean` — `ConjugationCodomain`
    instance diagnostic (`#verify_conjugation MyType`).
  - `Meta/Tactic/PureGuard.lean`, `NativeGuard.lean` — runtime
    axiom-purity / native-decide guards.
  - `tools/layer_audit.py` (repo root) — derive each file's natural
    vertical layer from import closure; reports violations +
    topical cluster depth.
  - `tools/sync_namespaces.py` — namespace ↔ path alignment.
  - `tools/scan_axioms.py` — per-module axiom audit.
  - `.claude/hooks/layer-import-guard.sh` — blocks new
    cross-ring reach-ins to `E213.<lower>.Internal.*` at edit-time.

## Distribution (per `tools/layer_audit.py`)

| top-folder      | Term | Theory | Lens | Lib | Meta | total |
|---|---|---|---|---|---|---|
| Term/           | 12  |   0  |  0  |   0  |  0  |   12 |
| Theory/         |  0  |  41  |  0  |   0  |  0  |   41 |
| Lens/           |  0  |   0  | 121 |   0  |  0  |  121 |
| Lib/Math/       |  —  |   —  |  —  | 743  |  —  |  743 |
| Lib/Physics/    |  —  |   —  |  —  | 165  |  —  |  165 |
| Meta/           |  0  |   0  |  0  |   0  | 37  |   37 |

Total: 1127 .lean files.

(Lib files each live at one natural vertical layer.  Per the 4-ring
spec, Lib/Math + Lib/Physics use Lens API only — they don't reach
into Theory or Term directly.)

Architecture audits (completed):
  - 4-ring + Meta finalised 2026-05-12 (rename of Kernel→Term,
    Firmware→Theory, Hypervisor→Lens; OS/ dissolved earlier).
  - App/ dissolved 2026-05-13 (Simplex.lean → Lib/Math/Combinatorics).
  - Universal-Lens witnesses moved Meta → Lens 2026-05-13.
  - NatHelpers moved Lib/Math → Meta/Nat 2026-05-13.
  - Term/Tactic moved to Meta/Tactic 2026-05-12.
  - Ring-discipline (Term ⊆ Theory ⊆ Lens ⊆ Lib + Meta any-ring)
    hook-enforced at edit-time.

## Branch

  - Current: `claude/encapsulate-ring-structure-CLeEG` —
    Lean 4 native encapsulation pass (private + protected on
    framework rings).  See `HANDOFF.md`.
