# lean/E213/Physics/ — sub-cluster index

Post-2026-05-05 consolidation marathon: **226 files** across 16 sub-
trees + 2 root umbrella aggregators (`Library.lean`, `Substrate.lean`).
Earlier `Phase{1Final,2,3,4}.lean` root files and `Phase{2,3,4}/`
sub-directories no longer exist (content distributed by topic).

## Layout

```
Physics/
├── Library.lean              (root umbrella: imports all of Library/)
├── Substrate.lean            (root umbrella: imports all of Substrate/)
│
├── AlphaEM/                17 files — α_em chain: Core, V137, V137Tight,
│                                       Derivation, GramSelfEnergy,
│                                       MasterCapstone, Milestone,
│                                       NUniverseCandidates, Prefactors,
│                                       Propagator, SO10, Simplicial,
│                                       StructuralGap, Structure, Tight,
│                                       Unified [V137Tighter merged in],
│                                       WithTail
├── Atomic/                 11 files + IE/ subdir (15 files)
│                                       BondAngles, Bridge, Complete1,
│                                       Enumeration, Expr, Helium,
│                                       Hydrogen, Reps, Screening,
│                                       Sparsity, SuperHeavyPredictions
│                                       + IE/{Beryllium, Boron, Capstone,
│                                       CNOFNe, HeliumPPM, HundPenalty,
│                                       HydrogenPPM, Hydrogenic,
│                                       IonizationEnergies, Lithium,
│                                       Period3, Period4, PeriodClosures,
│                                       PeriodicTable, SecondRow}
├── AtomicCorrespondences/  58 files — modern-physics translation
│                                       catalog (35+ topical files +
│                                       Capstone, MasterCatalog,
│                                       AtomicSuperCatalog;
│                                       Phase1CrossLink deleted
│                                       2026-05-05)
├── Basel/                   2 files — Bound (loose + tight endpoints
│                                       merged), WhyBasel
├── Cosmology/               6 files — Bridge, DarkEnergy,
│                                       HubbleConstant, NeffDerivation,
│                                       GravityShadow, HorizonInformation
├── Couplings/              17 files — α_GUT, AsymptoticFreedom,
│                                       ColorConfinement, SpectrumComplete,
│                                       GUTUnification, MasterUnification,
│                                       RunningGap, TripleCoupling
│                                       (v1+v2 merged), ClosedPropagator,
│                                       DysonStructure, ThetaQCD,
│                                       LambdaQCDPhantom, ParitySign,
│                                       PhotonKernel, CassiniLink,
│                                       PropagatorFamily, StaticCouplings
├── Foundations/            19 files — DrltZeroParameters, MasslessParticles,
│                                       FractalLensCardinality,
│                                       NUniverseFractalDepth/FromFractal,
│                                       ResolutionDepth,
│                                       FiniteUniverse/ResonanceN,
│                                       LensCardinalityFractalLevels,
│                                       GoldenRatio, FibonacciAtomic/Extended,
│                                       KoideFormula, HopHypothesis,
│                                       TightenBracket, UnifiedPattern,
│                                       IntegerLockings, CorrectionAsLens,
│                                       PureLens213
├── Hadron/                  8 files — Bigrading, Bridge, Masses,
│                                       NeutronProton, ProtonElectronRatio,
│                                       ProtonG, ProtonMass, QuarkHierarchy
├── Higgs/                   4 files — Mass, Master, Quartic, Vacuum
├── Library/                27 files — topical quick-lookup catalogs
│                                       (one per physics field)
├── Mass/                    3 files — MuOverE, TauOverMu, HierarchyTowers
├── Mixing/                  5 files — CKMHierarchy, CPViolation,
│                                       CabibboAngle, Bridge, NeutrinoMixing
├── Nuclear/                 6 files — DeuteronBinding, MagicNumbers,
│                                       MagicNumbersAtomic, Binding,
│                                       Bridge, Shells
├── Simplex/                 7 files — Counts, SubInventory, FoccSpectrum,
│                                       FaceTerms, MultiComposite,
│                                       GenerationStructure, Generations
├── Substrate/              13 files — Capstone, Edges, Existence,
│                                       Falsifier, Force, Lens, Observable,
│                                       Origin, Pairs, Phase1Bridge, Shape,
│                                       Space, Time
└── YangMills/               6 files — WZBosons, WeinbergAngle, Bridge,
                                       Gap, SU5Roots, WMassFalsifier
```

OS-layer capstones live separately at `lean/E213/OS/Physics/Capstones/`
(8 files: Capstone, MasterCatalog, ValidationStandardOne,
PureAtomicObservables, FinitistObservableChain, PhysicsTrackComplete,
Paper2Bundle, Paper3Bundle, Phase3Capstone, UltraCapstone, MegaCapstone,
FinalCapstone, AbsoluteAtomicCapstone — orchestration of Physics/
sub-capstones).

## Naming convention

When a sub-cluster name appears as a prefix in a file name, the
prefix is dropped (e.g., `HadronBridge.lean` → `Hadron/Bridge.lean`,
`NuclearBinding.lean` → `Nuclear/Binding.lean`).

V-prefix on digit-start names (`V137.lean` substitutes for "1/137"
since Lean module names cannot start with digit).  See
`lean/E213/ARCHITECTURE.md` §"V-prefix on digit-start" for guidance
on when V-prefix is appropriate; sequential variants prefer
descriptive topic names instead.

## Internal namespace declarations

File-system path was reorganized; namespace declarations inside
files were retained.  Lean's module-path and namespace are
independent — `import E213.Physics.AlphaEM.V137` brings in
theorems defined under `namespace E213.Physics.AlphaEM.V137`.

## 2026-05-05 consolidation marathon

35 files deleted across 11 sub-trees (240 → 205 Physics-tree files at
peak; current count includes citation-sweep edits).  Patterns
verified:
  - Phase3Derivation/Manifesto/Reframing trace: 9/9 alias-only
  - Falsifier-named pure decide bundle: 5/5
  - True-marker (`theorem foo : True := ...`): 3/3
  - *Finitist transitive-only wrapper: 3/3
  - *Specific transitive-only wrapper: 3/3
  - Strict-extension merge (Basel pattern): 3/3
    (Basel/BoundTight, TripleCoupling/V2, V137/Tighter)

See `research-notes/CONSOLIDATION_PROTOCOL.md` for the procedure
applied + cumulative pattern table.

## See also

  - `lean/E213/INDEX.md` — full library map
  - `lean/E213/ARCHITECTURE.md` — canonical layer architecture
  - `Physics/Library.lean` — Library/ umbrella aggregator
  - `Physics/Substrate.lean` — Substrate/ umbrella aggregator
