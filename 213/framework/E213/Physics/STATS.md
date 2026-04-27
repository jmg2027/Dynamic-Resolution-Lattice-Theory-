# Physics Track Stats — Phase 1 (50 files)

## 파일 카운트

| 카테고리 | 파일 수 | 주요 내용 |
|---|---|---|
| Foundation | 4 | SimplexCounts, FoccSpectrum, BaselBound, BaselSimplicial |
| α_em chain | 9 | AlphaGUT, AlphaEM, AlphaEM137, RunningGap, Unified, Derivation, Prefactors, AlphaEMSimplicial, AlphaEMTight |
| Couplings | 3 | WhyBasel, NeffDerivation, ResolutionDepth |
| Masses | 6 | MuOverE, TauOverMu, ProtonMass, HiggsMass, HiggsQuartic, NeutronProton |
| Mixing | 3 | CabibboAngle, NeutrinoMixing, CKMHierarchy |
| Hadrons/Nuclear | 3 | HadronMasses, NuclearBinding, MagicNumbers |
| Atomic | 4 | HydrogenAtom, HeliumAtom, AtomicScreening, BondAngles |
| Cosmology | 2 | DarkEnergy, HiggsVacuum |
| Predictions | 2 | Generations, ThetaQCD |
| Geometric | 4 | PhotonKernel, FaceTerms, GoldenRatio, FibonacciAtomic |
| Universal patterns | 3 | DysonStructure, ClosedPropagator, WZBosons |
| Capstones | 5 | Capstone, AlphaEMSimplicial, UnifiedPattern, MasterCatalog, PhysicsTrackComplete |
| Meta + entry | 2 | Physics.lean, ROADMAP.md, README.md, STATS.md |

**총 50 Lean files + 4 docs.**

## 정리 카운트

대략 **300+ theorems**, 모두 0 sorry, 0 axiom (1 propext only).

## Atomic atoms (재등장 횟수)

| Atom | 등장 파일 |
|---|---|
| NS = 3 | 모든 파일 |
| NT = 2 | 모든 파일 |
| d = 5 | 모든 파일 |
| c_lat = 2 | 다수 |
| d² - 1 = 24 | α_em, m_μ, m_H, Ω_Λ, PMNS, λ_H, … (8+) |
| d - 1 = 4 | Dyson, Higgs, m_μ, Cabibbo, a_S, θ_QCD (6+) |
| d + 1 = 6 | 1/NS, m_τ, m_W/m_Z, a_V (4+) |
| NS² - 1 = 8 | α_3, λ_H denom, F_6 (3+) |
| c·NS·NT = 12 | α_2 prefactor, photon edges, Δm_np (3+) |
| NS·NT² = 24 | adjoint via α_2 |
| c·NS·NT·d = 60 | α_1 Y-norm |
| NS² = 9 | GMOR, F_? |
| NS²+NS+1 = 13 | NH₃, F_7 |
| F_3..F_7 = 2,3,5,8,13 | Fibonacci atomic |

## 정밀 양 매치 종합

| 양 | DRLT | 관측 | 매치 |
|---|---|---|---|
| 1/α_em(IR) | 137.035 | 137.036 | ppm |
| m_μ/m_e | 206.7682837 | 206.7682838 | 0.48 ppb |
| m_p | 938.272 | 938.272 | exact |
| m_H | 125.28 GeV | 125.25 | +0.02% |
| Ω_Λ | 0.6850 | 0.685 | 0.0008% |
| sin²θ₁₃ | 0.0220 | 0.0220 | within 1σ |
| ν m₃/m₂ | 5.712 | 5.71 | +0.04% |
| η_B | 6.13×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.5% |
| Magic numbers | 7/7 | 7/7 | exact |
| m_π | 137.6 MeV | 137.3 | +0.2% |
| m_ρ | 782.1 MeV | 782.7 | -0.07% |
| Δ-N split | 295.7 MeV | 294 | +0.6% |
| sin θ_C | 5/22 | 0.22650 | 0.34% |

## Phase 1 종료 마커

50 files 누적.  Phase 2 (SM-frame artifact 식별) 진입 가능.
