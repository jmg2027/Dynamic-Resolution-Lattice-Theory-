# lean/E213/ — formal source of truth

The authoritative state of 213.  All other documents (theory/,
research-notes/, blueprints/, seed/) are entry points INTO this
body of work or derived artifacts.  The current narrative lives in
`theory/`.

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
Term/     ★ 17 files — implementation of Raw (deep-embedded Tree
            substrate, Bool comparators, Sound bridges, Pair/Rat,
            Decide, Demo, MonomialAxioms).  ★ literally 0-axiom.
  ↓
Theory/   24 files — the 213 axiom itself (Raw + 4-clause commitments)
            + Atomicity (forced d=5, (NS,NT)=(3,2))
            + CDDouble (generic Order-4 mechanism)
            + Raw sub-cluster (Slash/Swap/Fold/FoldSwap/Levels/
            Endomorphic/Rec/Demo/Congruence/
            ParenthesizationDistinct/SwapSlash).
  ↓
Lens/    144 files — Lens framework (catamorphism Raw → α).
            Algebra/ AxiomLenses/ Cardinality/ Compose/
            Instances/ Lattice/ Properties/ Universal/ Internal/
            Number/ sub-clusters + Initiality + SemanticAtom + EqPW
            + Congruence + SyntacticInternalization.
  ↓
Lib/Math/    727 files (42 sub-clusters): CayleyDickson, Real213,
             SignedCut, Probability, Cohomology, DyadicFSM,
             HodgeConjecture, Analysis, Linalg213, Cauchy,
             ModArith, Modulus, Irrational, Polynomial213,
             Trajectory, …
Lib/Physics/ 165 files (17 sub-clusters): AlphaEM, Couplings,
             Hadron, Higgs, Mass, Mixing, Nuclear, Cosmology,
             Atomic, Simplex, Basel, YangMills, Capstones,
             AtomicBase, Foundations, Certificates, …

Meta/    37 files (ring-independent) — Lean 4 bridge.
             SelfRecognising (CommBinary/NonVanishing/Conjugation
             Codomain typeclass tower), AxiomMinimality{,Capstone},
             LensInternality, BitPatternUniqueness, Tactic/
             (Nat213, Mod213, Fin213, Pow213, Omega213, QuadNorm,
              NativeGuard, PureGuard, VerifyConjugation,
              DeriveConjugationCodomain, List213), Nat/Int213/
              Algebra213 helpers.  Any ring may import from Meta.
```

## Layer roles

| Layer | Files | Role | Axiom load |
|---|---|---|---|
| Term/      | 17  | implementation of Raw (Tree, Term, comparators)  | ★ 0  |
| Theory/    | 24  | Raw axiom + Atomicity + CDDouble         | mostly 0 |
| Lens/      | 144 | Lens framework + sub-clusters            | mostly 0 |
| Lib/Math/  | 727 | 213-native mathematics (42 sub-clusters) | mixed |
| Lib/Physics/| 165| 213-native physics (17 sub-clusters)     | mixed |
| Meta/      | 37  | Lean 4 bridge (tactics + typeclasses)    | mostly 0 |

Total: 1114 .lean files.  Layer spec: `ARCHITECTURE.md`.

## Capstone navigation

Detailed theorem index: `CAPSTONE_INDEX.md` (root)
Strict-zero-axiom list: `STRICT_ZERO_AXIOM.md` (root)

Top achievements:
  - `Physics/PureAtomicObservables.pure_atomic_observables_capstone`
  - `Physics/AlphaEM/GramStructuralCapstone.invAlphaEm_precision_theorem`
    (0.2 ppb structural precision)
  - `Physics/AlphaEMMilestone.alpha_em_milestone`
    (CLAUDE.md "first milestone of rewriting physics from scratch")

## Where to read what

| Question | Where to look |
|---|---|
| "What does DRLT compute?"     | `Lib/Physics/Capstones/PureAtomicObservables.lean` + `CAPSTONE_INDEX.md` |
| "How does α_em derive?"       | `Lib/Physics/AlphaEM/` chain |
| "Where is the config count?"   | `Lib/Math/Cohomology/Fractal/ConfigCount.lean` (parametric, no privileged level) |
| "Why finite N only?"          | `Lib/Math/NumberSystems/Real213/Bisection/DyadicTrajectory.lean` (limit ≠ exact) + `LESSONS_LEARNED.md` |
| "What are the atomic primitives?" | `Theory/Atomicity/Five.lean` + `Theory/Atomicity/PairForcing.lean` |
| "How is Term ring 0-axiom?"   | `Term/` 12 files + `tools/kernel_regress.sh` + `STRICT_ZERO_AXIOM.md` |
| "Cohomology classes?"         | `Lib/Math/Cohomology/` (94 files in 11 sub-clusters) + `rust-engine/docs/cohomology-classes.md` |
| "Lens framework?"             | `Lens/LensCore.lean` + 9 sub-cluster umbrellas under `Lens/` + `Lens/Universal/Witnesses/` |
| "Universal-Lens witnesses?"   | `Lens/Universal/Witnesses/` |
| "Raw-native number types?"    | `Lens/Number/Nat213/{Raw,Core,Chain,Peano,Bridge,ChartGeneral}.lean` + `Lens/Number/Nat213/Tower/{NatPairToInt,NatPairToQPos,NatTripleToZ2}.lean` |
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

Ring-discipline (Term ⊆ Theory ⊆ Lens ⊆ Lib + Meta any-ring) is
hook-enforced at edit-time.
