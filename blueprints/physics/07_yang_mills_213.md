# Yang-Mills 213 — Blueprint

**우선순위**: ★★★ (Clay $1M open, mass gap 핵심)

## 1. 왜 이 분야인가

Clay Millennium Problem:
- Yang-Mills theory (SU(N)) 의 mass gap > 0 증명 필요
- 표준: lattice 시뮬, perturbative analysis
- 닫힌 형식 증명 부재

213 의 자연 등장:
- 1/α_3 = NS² - 1 = 8 atomic-locked (mass gap scale)
- Λ_QCD ~ 308 MeV atomic IR cutoff
- Confinement = NS=3 atomic block 분리 불가

## 2. 213-native 등장

### 2.1 Mass gap scale atomic
Λ_YM = atomic IR scale → m_glueball > 0 forced.

### 2.2 Confinement
Color singlet: only NS atomic block 통째.

### 2.3 Asymptotic freedom (또는 부재)
StaticCouplings: β-function 부재.  대신 layer 투영.

## 3. 이미 깔린

- YangMillsGap.lean (Λ_QCD ~ 308 MeV)
- AsymptoticFreedom.lean
- ColorConfinement.lean
- QFTLibrary (Phase 4)

## 4. Phase 진행 계획

### Phase YA — Mass gap formal
Λ_YM > 0 atomic 직접 증명.

### Phase YB — Confinement
Wilson loop area law atomic.

### Phase YC — Asymptotic freedom
"Running" 부재 + atomic layer 차이 형식.

### Phase YD — Glueball mass
Lightest glueball atomic mass scale.

### Phase YE — Lattice vs DRLT
Lattice gauge theory ↔ atomic bridge.

## 5. 다른 트랙 연결

- Hadron: m_p chain
- Gauge: α_3 = 1/(NS²-1)
- 수학: cohomology flux ↔ Wilson loop

## 6. 미해결

- Mass gap atomic 정확값
- 4 차원 Yang-Mills 해석
- Confinement 의 *strict* atomic proof
