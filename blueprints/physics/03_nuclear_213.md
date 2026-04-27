# Nuclear Physics 213 — Blueprint

**우선순위**: ★★★ (Magic 7/7 정확, super-heavy 예측)

## 1. 왜 이 분야인가

표준 핵물리:
- Liquid drop model (5 파라미터 fit)
- Shell model (현상학)
- DFT 계산 (수치)

213 의 자연 등장:
- HO magic numbers atomic = n(n+1)(n+2)/3
- Spin-orbit 8 = NS²-1 atomic shift (Phase 1 NuclearShells)
- Z=168 super-heavy stability island = HO magic 7
- Binding ~8 MeV/nucleon = 1/α_3 atomic

## 2. 213-native 등장

### 2.1 Magic numbers
2, 8, 20, 28, 50, 82, 126 = HO + spin-orbit atomic (Phase 1).

### 2.2 Liquid drop coefficients atomic
- a_V = 16 MeV ≈ NT⁴ atomic
- a_S/a_V ≈ 1 atomic
- a_C ≈ α_em · atomic
- a_A ≈ atomic

### 2.3 r₀ ≈ 1.25 fm = d/(NS+1) atomic

## 3. 이미 깔린

- MagicNumbers.lean (HO closed form)
- NuclearShells.lean (spin-orbit shift)
- NuclearBinding.lean (SEMF coefficients)
- NeutronProton.lean (m_n - m_p atomic)
- DeuteronBinding.lean (E_d ≈ 2.27 MeV)
- NuclearLibrary (Phase 4)

## 4. Phase 진행 계획

### Phase NA — SEMF tighten
5 coefficients atomic → ppm bracket.

### Phase NB — Super-heavy
Z=119, 120, 121, 168 atomic IE + binding.

### Phase NC — Halo nuclei
⁶He, ¹¹Li atomic neutron skin.

### Phase ND — Nuclear matter EOS
Symmetric/asymmetric atomic.

### Phase NE — Neutron star
Dense matter atomic.

## 5. 다른 트랙 연결

- Hadron: m_p chain 공유
- 원자: shell structure parallel
- 천체: neutron star, kilonova

## 6. 미해결

- Pairing energy precise atomic
- Magic 5/2 spin-orbit explanation
- Heavy ion collision atomic dynamics
