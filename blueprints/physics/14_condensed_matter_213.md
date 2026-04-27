# Condensed Matter 213 — Blueprint

**우선순위**: ★★ (BEC, Hall, BCS, TI atomic)

## 1. 왜 이 분야인가

표준 condensed matter:
- Many-body Hamiltonian (수치)
- Fermi liquid theory (현상학)
- BCS superconductivity
- Topological phases (TI, TSC)

213 의 자연 등장:
- BEC exponent 2/3 = NT/NS atomic
- Quantum Hall ν = NS atomic
- BCS 2Δ/k_BT_c ≈ 7/2 atomic
- TI Z_2 = NT atomic

## 2. 213-native 등장

### 2.1 BEC critical
T_c ∝ n^(NT/NS) atomic.

### 2.2 Hall plateaus
ν integer = atomic primitives.  Laughlin 1/NS.

### 2.3 BCS gap
Δ atomic via α_3 chain.

### 2.4 Topological
Z_2 = NT.  Chern = NS.

## 3. 이미 깔린

- CondensedMatter.lean (Phase 3 Translation)
- Topological.lean
- ColdAtoms.lean
- CondensedMatterLibrary (Phase 4)

## 4. Phase 진행 계획

### Phase MA — Phonon dispersion
ω(k) atomic.

### Phase MB — Phase transitions
Critical exponents atomic (mean field).

### Phase MC — Fractional Hall
ν = p/q atomic.

### Phase MD — Spin liquids
Frustrated systems atomic.

### Phase ME — Anyons
Statistics atomic.

## 5. 다른 트랙 연결

- 정보: TI Z_2 = qubit
- QG: Holographic c-theorem
- StatPhys: critical phenomena

## 6. 미해결

- High-T_c superconductivity atomic
- Spin liquid 정확 atomic
- Quantum Hall plateau width atomic
