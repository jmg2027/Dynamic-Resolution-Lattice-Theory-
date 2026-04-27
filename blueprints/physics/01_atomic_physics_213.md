# Atomic Physics 213 — Blueprint

**우선순위**: ★★★ 최우선 (Phase 4 IE 도서관 이미 깔림)

## 1. 왜 이 분야인가

표준 atomic physics:
- Schrödinger 식 + 다체 양자역학 (NP-hard)
- Slater rules (~5-10% 정밀도, ad hoc)
- Hartree-Fock + 상관 에너지 (변분/perturb)

213 의 자연 등장:
- Phase 4 HydrogenIE: **4.3 ppb formal Lean** verification
- Phase 4 Library: 28 sub-libraries, IE/atomic chain
- Period closures *모두* atomic (Phase 4 PeriodClosures)
- Hund 규칙 = α_3 atomic penalty (Phase 4 HundPenalty)
- Closed propagator P(x) atomic correction universal

## 2. 213-native 등장

### 2.1 Periodic table atomic
113 + 5 super-heavy 원소 모두 atomic 표현 (Phase 4
CompletePeriodicTable).  Z=168 = HO magic 7 예측.

### 2.2 σ_atomic catalog
- σ_1s_to_outer = 7/8
- σ_2s_to_2s = NS/d
- σ_2s_to_2p = 17/(4d)
- σ_2p_to_2p = (NS²+NT)/(d·NS)

각 σ atomic primitives 비.

### 2.3 P(x/k) family
모든 correction = closed propagator P(x/k_Z) atomic.

## 3. 이미 깔린 building blocks

- HydrogenIEPPM.lean (4.3 ppb)
- HeliumIEPPM, LithiumIE, BerylliumIE, BoronIE
- CNOFNeIE, Period3IE, Period4-7IE
- HundPenalty, PropagatorFamily
- IECapstone, CompletePeriodicTable

## 4. Phase 진행 계획

### Phase EA — IE ppm refinement (Z=2-10)
He, Li, Be, B 의 σ atomic 추가 항 → ppm.

### Phase EB — Hund 일반화 (s/p/d 모두)
ε_pair atomic = R · NS/(NS²-1) 의 d-shell 확장.

### Phase EC — Lanthanide/Actinide
Z=57-71, 90-103 atomic chain.

### Phase ED — Atomic spectroscopy
Rydberg series, fine structure, hyperfine splitting.

### Phase EE — Molecular
H₂, O₂, N₂ binding energy + bond length atomic.

## 5. 다른 트랙 연결

- 핵 트랙: nuclear binding ~ 1/α_3 = 8 MeV
- 우주론: 항성 핵합성 atomic
- 수학 트랙: Phase 4 Library = 카탈로그 모듈

## 6. 미해결

- Lanthanide 4f shell 의 σ_atomic
- Spin-orbit coupling atomic 도출
- QED Lamb shift atomic chain
