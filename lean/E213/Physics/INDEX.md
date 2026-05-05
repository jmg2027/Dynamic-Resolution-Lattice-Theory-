# lean/E213/Physics/ — sub-cluster index

After 2026-05-01 reorg: 121 → 4 flat-root files (-97%);
content distributed into 18 sub-clusters.

## Layout

```
Physics/
├── Phase1Final.lean         (root: namespace aggregator)
├── Phase2.lean              (root: namespace aggregator)
├── Phase3.lean              (root: namespace aggregator)
├── Phase4.lean              (root: namespace aggregator)
├── Phase2/   13 files — pre-finitist phase 2 derivations
├── Phase3/   91 files — pre-finitist phase 3 derivations
├── Phase4/   52 files — pre-finitist phase 4 (Library/ catalog)
│
├── AlphaEM/             17 — α_em chain (Core, V137{,Tight}, Derivation,
│                              GramSelfEnergy, MasterCapstone, Milestone,
│                              NUniverseCandidates, Prefactors, Propagator,
│                              SO10, Simplicial, StructuralGap, Structure,
│                              Tight, Unified [V137Tighter merged in],
│                              WithTail).
│                              (Phase3Derivation + Phase3Sharp deleted,
│                              V137Tighter merged into Unified 2026-05-05)
├── Couplings/           17 — α_GUT, asymp.freedom, color confinement,
│                              SpectrumComplete, GUTUnification, MasterUnif.,
│                              RunningGap, TripleCoupling (v1+v2 merged),
│                              ClosedPropagator, DysonStructure, ThetaQCD,
│                              LambdaQCDPhantom, ParitySign, PhotonKernel,
│                              CassiniLink, PropagatorFamily, StaticCouplings
│                              (AlphaGUTPhase3Derivation +
│                              ThetaQCDFalsifier deleted, TripleCouplingV2
│                              merged into TripleCoupling 2026-05-05)
├── Foundations/         16 — DrltZeroParameters, MasslessParticles,
│                              FractalLensCardinality,
│                              NUniverseFractalDepth/FromFractal,
│                              ResolutionDepth, FiniteUniverse/ResonanceN,
│                              LensCardinalityFractalLevels, GoldenRatio,
│                              FibonacciAtomic/Extended, KoideFormula,
│                              HopHypothesis, TightenBracket, UnifiedPattern
├── Hadron/              8  — Bigrading, Bridge, Masses, NeutronProton,
│                              ProtonElectronRatio, ProtonG, ProtonMass,
│                              QuarkHierarchy
│                              (ProtonMassPhase3Derivation +
│                              ProtonMassSharp deleted 2026-05-05)
├── Mass/                3  — MuOverE, TauOverMu, HierarchyTowers
│                              (MuOverEFinitist, NoFourthGen,
│                              LeptonRatios, LeptonRatioPhase3Derivation,
│                              NeutrinoRatioPhase3Derivation deleted
│                              2026-05-05 as orphan/transitive-only)
├── Higgs/               4  — Mass, Master, Quartic, Vacuum
│                              (MassFinitist + Phase3Derivation
│                              deleted 2026-05-05 as orphan traces)
├── Nuclear/             6  — DeuteronBinding, MagicNumbers{,Atomic},
│                              Binding, Bridge, Shells
│                              (MagicNumbersFalsifier +
│                              MagicNumbersPhase3Derivation deleted
│                              2026-05-05 as alias-only orphans)
├── Mixing/              5  — CKMHierarchy, CPViolation, CabibboAngle,
│                              Bridge, NeutrinoMixing
├── Cosmology/           6  — Bridge, DarkEnergy, HubbleConstant,
│                              NeffDerivation, GravityShadow,
│                              HorizonInformation
│                              (DarkEnergyPhase3Derivation +
│                              OmegaLambdaFinitist + HubbleTension
│                              deleted 2026-05-05 as alias-only orphans)
├── Atomic/              5  — Bridge, Screening, BondAngles, Helium, Hydrogen
├── Simplex/             7  — Counts, SubInventory, FoccSpectrum, FaceTerms,
│                              MultiComposite, GenerationStructure, Generations
├── Basel/               2  — Bound (S(N) + upper + lower_tight,
│                              merged from BoundTight 2026-05-05),
│                              WhyBasel (1/n² propagator justification)
├── YangMills/           5  — WZBosons, WeinbergAngle, Bridge, Gap, SU5Roots
└── Capstones/           8  — Capstone, MasterCatalog, ValidationStandardOne,
                              PureAtomicObservables, FinitistObservableChain,
                              PhysicsTrackComplete, Paper2Bundle, Paper3Bundle
```

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
theorems defined under `namespace E213.Physics.AlphaEM137`.

## See also

  - `lean/E213/INDEX.md` — full library map
  - `Physics/Phase4/Library/README.md` — Library/ sub-tree
