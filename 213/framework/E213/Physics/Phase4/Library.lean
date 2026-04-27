import E213.Physics.Phase4.Library.IEMethodology
import E213.Physics.Phase4.Library.AtomicFunctions
import E213.Physics.Phase4.Library.PeriodicCatalog
import E213.Physics.Phase4.Library.AtomicMassLibrary
import E213.Physics.Phase4.Library.CouplingLibrary
import E213.Physics.Phase4.Library.MathLibrary
import E213.Physics.Phase4.Library.CosmologyLibrary

/-!
# Phase 4 Library — IE 도서관 + 다른 분야 framework

★ User directive ★
"이런 식으로 모든 IE 를 완전 계산하는 방법론 + 주기율표
새로 작성.  라이브러리화 + 카탈로그화.  다른 물리 + 수학 도
거대한 도서관 + 라이브러리"

## 현재 (IE)

  IEMethodology.lean    — IE 계산 절차 (8 step)
  AtomicFunctions.lean  — 재사용 σ, hund_count, ...
  PeriodicCatalog.lean  — 주기율표 Z=1-36 atomic 검증

## 향후 도서관 확장 plan

### Physics Library
  AtomicMassLibrary    — 원자 질량 atomic chain
  HadronMassLibrary    — 하드론 질량 (Phase 1 → library)
  CouplingLibrary      — α_em, α_GUT, α_3, ...
  PMNSLibrary          — neutrino mixing matrix
  CKMLibrary           — quark mixing matrix
  CosmologyLibrary     — Ω_Λ, η_B, H_0, T_CMB
  NuclearLibrary       — magic numbers, binding, radii
  MolecularLibrary     — bond angles, lengths, IE
  PhasesLibrary        — phase transitions, critical exponents
  ParticleLibrary      — decay rates, branching ratios

### Math Library
  PrimesLibrary        — atomic primes (2, 3, 5, 7, 13, 41, 137)
  FibonacciLibrary     — F_n atomic identifications
  CombinatoricsLibrary — C(d, k), permutations atomic
  GroupTheoryLibrary   — SU(NS), SU(NT), SU(d) atomic
  GeometryLibrary      — simplex, polytope counts
  TopologyLibrary      — cycle space, b_n, Euler char

각 라이브러리:
  * 재사용 atomic functions
  * 카탈로그 (정리된 항목 list)
  * Lean theorems (decide-checked)

전체: 거대 atomic 도서관.
-/
