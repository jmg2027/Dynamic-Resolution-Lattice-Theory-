# Chunk E — Analysis audit

**Clusters**: Analysis (77), CascadeCalculus (2), ODE (5),
Multivariable (9), Functional (5), Measure (5), Trajectory (1).
Total **104 files** (수정: 이전 ~98 추정 → 정확 104).

**Audit date**: 2026-05-12.

## §0 Summary

| Cluster | Files | Lines | Spec status |
|---|---|---|---|
| Analysis/        | 77 | 10815 | ✓ clean (largest in Math by lines) |
| CascadeCalculus/ | 2  |  174 | ✓ |
| ODE/             | 5  |  291 | ✓ |
| Multivariable/   | 9  |  599 | ✓ |
| Functional/      | 5  |  299 | ✓ |
| Measure/         | 5  |  396 | ✓ |
| Trajectory/      | 1  |   90 | ✓ |

Chunk total = **0 violations**.  매우 깨끗.

## §1 Ring violations

**0**.  chunk F (DyadicFSM) 와 같이 perfectly clean.

## §2 Cluster docstring overview

### Analysis/ (77 files, 7 sub-dirs + 13 top-level)

213-native calculus on Real213 cuts.

| Sub-dir | Files | Lines | Topic |
|---|---|---|---|
| ClassicCalc/      | 3 |  474 | classical calculus structure on cuts |
| Differentiation/  | 14 | 2182 | differential calculus (PolySumDerivative, ResolutionDepth) |
| DyadicSearch/     | 9 | 2859 | dyadic-search IVT apparatus (DyadicBracket, DyadicRiemann, DyadicTrajectory, MinimalRootLensMonotone, UnitConsistentOracles) |
| **FluxMVT/**      | **22** | **2926** | flux-form Mean Value Theorem (가장 큰 sub-dir) |
| Integration/      | 10 |  934 | Riemann + dyadic integration |
| ODE/              | 3 |  249 | ODE on cuts (Analysis 내부) |
| Series/           | 3 |  151 | series convergence |

**Top-level 13**:
- aggregators (7): ClassicCalc, Differentiation, DyadicSearch,
  FluxMVT, Integration, ODE, Series
- Cauchy-related content (4): BracketCauchyModulus,
  CauchyComplete, CauchyProj, ChainCauchy
- Misc (2): ResolutionShift (400 줄, (Nat,+) grading on cut
  transformers), PhysicsBridgeNT2

### CascadeCalculus/ (2 files)

Propext-extermination work 의 cascade-delete pattern model.
- Core (99): minimal model + seed
- Instance (75): branch-instance test case

명확한 *audit / refactor 도구* 성격 — fold 후보: Math/Tactic/ 또는
research-notes/.

### ODE/ (5 files) — Math 차원의 ODE

213-native paradigm: ODE solution = Picard iteration trajectory.
- Capstone, HeatEqDiscrete, LinearODE, PicardIterate, WaveEqDiscrete

주의: **Analysis/ODE/ 도 따로 존재** (3 files).  중복 가능성 검토.

### Multivariable/ (9 files)

213-native multivariable calculus + Stokes.
- MultiCut, PartialDerivative, Gradient, MultiIntegral, Stokes,
  Stokes2D, Stokes3D, Capstone (8 + ?)

### Functional/ (5 files)

Functional analysis on finite-grid Nat → Nat.
- InnerProduct, LinearOperator, Norm, Spectrum, Capstone

### Measure/ (5 files)

Choice-free dyadic measure theory.
- MeasurableSet (dyadic bracket list, σ-algebra 없음),
  DyadicMeasure, LebesgueIntegral, Lp, Capstone

### Trajectory/ (1 file)

PhaseChiralBridge — K_{3,2}^{(2)} 의 두 ∅-axiom decomposition bridge.
**Tiny cluster** → fold candidate (SignedCut 또는 Cohomology 와 가까움).

## §3 Naming + 조직 평가

### Analysis 내부 ODE 와 top-level ODE 중복

- `Lib/Math/Analysis/ODE/` (3 files, 249 lines) — Analysis 내부
- `Lib/Math/ODE/` (5 files, 291 lines) — top-level

같은 주제 두 위치.  내용 비교 필요 — 통합 또는 명확한 역할 분리.
후보: Analysis/ODE/ 를 top-level ODE/ 로 통합.

### Tiny cluster fold candidates

- **Trajectory/** (1 file) → SignedCut/ 또는 Cohomology/ 또는
  Lens/Codomain/ (PhaseChiralBridge 의 의미에 따라).
- **CascadeCalculus/** (2 files) → Tactic/ 또는 research-notes/
  (propext-extermination audit 도구).

### Naming OK

- Analysis, ODE, Multivariable, Functional, Measure, Trajectory —
  명확.
- CascadeCalculus — 의미 명확 (cascade-delete calculus) 하나 짧음.

### INDEX.md / API.lean 추가 권장

- Analysis/INDEX.md, API.lean — 77 files 큰 cluster, navigation
  도움.
- 각 sub-dir 의 INDEX.md (FluxMVT 22 files 가장 절실).
- ODE/, Multivariable/, Functional/, Measure/ — INDEX.md 권장
  (각 5–9 files).

### FluxMVT/ 22 files — 큰 sub-cluster

Analysis 의 가장 큰 sub-dir.  자체 organization 검토 가치 있음
(별도 audit pass).

## §4 Axiom status

Explore agent: **~85% PURE** for Analysis (dyadic-search IVT,
differentiation 이 omega-free).  다른 cluster 들도 비슷.

ResolutionShift (400 lines, top-level) 가 가장 큰 단일 파일 —
(Nat,+) grading 위 cut transformer 구조 explore.  PURE 여부 미확인.

Multivariable, Functional, Measure, ODE 의 capstone 들 명시적으로
"All ∅-axiom" — 거의 100% PURE 추정.

## §5 처리 priority

### Quick wins

1. **Trajectory/** fold → SignedCut/ 또는 Cohomology/ (의미 따라).
2. **ODE 중복 해결** — Analysis/ODE/ ↔ top-level ODE/ 통합 또는
   역할 분리.
3. **Analysis/INDEX.md, API.lean** 추가.

### Mid-term

4. **FluxMVT/ (22 files) sub-organization** 검토 (별도 audit).
5. **CascadeCalculus/** 위치 재검토 — Math/Tactic 또는
   research-notes 이동.
6. **ResolutionShift** (400 lines) — content audit + sub-divide
   가능성.

### Long-term

7. **Multivariable Stokes 3 파일** (Stokes, Stokes2D, Stokes3D) —
   parametric n 으로 통합 가능성.
8. **Real213 ↔ Analysis 상호참조** — chunk B (Real213) 와의 cross-ref.

## §6 결정 보류

§3 fold/통합, §5 priority 모두 **기록만**.

특이사항:
- **0 violations + ~85% PURE** — chunk E 도 Math 의 axiom hygiene
  best 중 하나 (F, G 와 함께 상위 3 chunks).
- **Math 의 ODE 중복** (Analysis/ODE 와 top-level ODE) 가 명확한
  redundancy.
- **Analysis 가 lines 기준 Math 의 가장 큰 cluster** (10815) —
  77 files 의 navigation 위해 INDEX.md / API.lean 가치 큼.
- ResolutionShift 의 (Nat, +)-graded cut transformer 가 chunk E
  내 가장 특이한 단일 파일 — Analysis 외 cluster 와 연결 가능성.
