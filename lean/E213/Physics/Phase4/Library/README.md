# Phase 4 Library — DRLT 거대 atomic 도서관

★ User directive ★
> "모든 IE 완전 계산 방법론 + 라이브러리화 + 카탈로그화.
>  다른 물리·수학도 거대 도서관."

## 17 모듈 구조

### Methodology (3)
- `IEMethodology` — IE 계산 8 step 절차 + atomic σ catalog
- `AtomicFunctions` — sigma_inner, hund_count 재사용 함수
- `PeriodicCatalog` — Z=1-36 atomic 표현 검증

### Physics (10)
- `AtomicMassLibrary` — 원자량 (m_He/m_H = NT² 등)
- `CouplingLibrary` — α_em, α_GUT, α_3, α_2 atomic
- `CosmologyLibrary` — Ω_Λ, e-folds, Cassini
- `HadronMassLibrary` — m_p, π, ρ, J/ψ atomic
- `PMNSLibrary` — neutrino mixing (θ_ij, δ_CP)
- `CKMLibrary` — Wolfenstein λ = 5/22
- `NuclearLibrary` — magic numbers, HO closed form
- `MolecularLibrary` — bond angles (CH₄, H₂O, NH₃)
- `ParticleLibrary` — 192 = 8·24 muon lifetime
- `LeptonMassLibrary` — m_μ/m_e, m_τ/m_μ
- `StatPhysLibrary` — Stefan-Boltzmann, equipartition

### Math (4)
- `MathLibrary` — primes, Fibonacci, group theory
- `GeometryLibrary` — 5-simplex Δ⁴ 면 분포
- `TopologyLibrary` — Euler χ, cycle dim, Z₂

### Future Plan
- QFTLibrary, GRLibrary, QGLibrary, OpticsLibrary,
  PlasmaLibrary, CondensedMatterLibrary, ColdAtomsLibrary,
  AnomaliesLibrary, BeyondSMLibrary, ...

## 사용법

```lean
import E213.Physics.Phase4.Library

open E213.Physics.Phase4.Library.CouplingLibrary

-- atomic 결합 상수 즉시 사용
#check inv_alpha_3_eq_8  -- 1/α_3 = 8 atomic
```

## 운영 원칙

- 표준 수학·물리 차용 부재
- atomic primitives (NS=3, NT=2, d=5, c=2) 만
- 0 sorry, decide-checked
- 재사용 가능 catalog
