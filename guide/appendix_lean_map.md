# Appendix B — Lean Module Map

Reverse map: for each major `lean/E213/` directory, the guide
chapter(s) where its content is treated.

## Foundation layer (Mathlib-free, axiom-free Kernel)

| Lean directory | Files | Guide chapter(s) |
|----------------|-------|------------------|
| `Firmware/` | 13 | Ch. 00, Ch. 01 |
| `OS/` | 8 | Ch. 00, Ch. 02 |
| `Meta/` | 9 | Ch. 15 |
| `Tactic/` | 10 | Ch. 15 |
| `Infinity/` | 9 | Ch. 14 (extension) |
| `Hypervisor/` | 1 | Ch. 15 |
| `App/` | 1 | Ch. 03 (simplex) |
| `Kernel/` | 14 | Ch. 06, Ch. 07, Ch. 11 (Cap_Physics*) |

## Math (analysis 213)

| Lean directory | Files | Guide chapter(s) |
|----------------|-------|------------------|
| `Math/` | 8 | Ch. 14 (foundation) |
| `Research/Real213*` | 176 | Ch. 14 (full body) |
| `Research/CayleyDickson/` | (selected) | Ch. 01 (alt substrate) |
| `Research/F9Lens` | 1 | Ch. 01 (alt substrate) |

## Physics (Phase 1–4)

| Lean module / pattern | Guide chapter |
|-----------------------|---------------|
| `SimplexCounts`, `FoccSpectrum` | Ch. 03 |
| `BaselBound`, `WhyBasel` | Ch. 03, Ch. 05 |
| `AlphaGUT`, `AlphaEM`, `AlphaEM137`, `AlphaEM137Tight`, `BaselBoundTight`, `AlphaEMStructuralGap`, `GUTUnification` | Ch. 05 |
| `MuOverE`, `TauOverMu`, `ProtonMass`, `HiggsMass` | Ch. 06 |
| `QuarkHierarchy`, `HierarchyTowers` | Ch. 06 |
| `CabibboAngle`, `CKMHierarchy`, `NeutrinoMixing`, `CPViolation` | Ch. 08 |
| `HadronMasses`, `ColorConfinement`, `AsymptoticFreedom`, `QCD` | Ch. 10 |
| `MagicNumbers`, `NuclearBinding`, `NuclearShells`, `DeuteronBinding` | Ch. 11 |
| `Phase4/HydrogenIEPPM`, `Phase4/Library/Period{1..7}IE` | Ch. 04, Ch. 07 |
| `Phase4/Library/AtomicMassLibrary` | Ch. 07 |
| `AtomicScreening`, `BondAngles`, `HydrogenAtom`, `HeliumAtom` | Ch. 07 |
| `DarkEnergy`, `HubbleConstant`, `GravityShadow` | Ch. 09 |
| `BaryonAsymmetry` | Ch. 09 |
| `YangMillsGap`, `PhotonKernel` | Ch. 12 |
| `FibonacciAtomic`, `FibonacciExtended` | Ch. 02 |
| `GenerationStructure`, `SU5Roots` | Ch. 02, Ch. 08 |
| `DysonStructure`, `ClosedPropagator`, `FaceTerms` | Ch. 03 |
| `ThetaQCDFalsifier`, `WMassFalsifier`, `MagicNumbersFalsifier` | Ch. 15 |

## Phase tracking

| Phase | Files | Status | Guide |
|-------|-------|--------|-------|
| Phase 1 | 68 | Complete | Ch. 02–11 (foundation) |
| Phase 2 | (selected) | Falsifier track | Ch. 15 |
| Phase 3 | (selected) | Translation layer | Ch. 05, Ch. 11 |
| Phase 4 | 20+ | Library | Ch. 04, Ch. 07 |

## Notes on coverage

- Every chapter except Ch. 13 (RH/Millennium) has at least one
  associated Lean module.
- Ch. 13 is the largest open marathon — paper5/7/9/10/11/12/13/15/16
  are all external-only.
- `Research/Real213*` (176 files) is the single largest body of
  213-internal mathematics; treated in Ch. 14.
- `lean/E213/Physics/Phase4/Library/` covers periodic table to ppb;
  treated in Ch. 04 (formula) + Ch. 07 (table).
