# Particle Physics 213 — Blueprint

**우선순위**: ★★ (Decay, scattering, lifetimes)

## 1. 왜 이 분야인가

표준 입자물리:
- Decay rate Γ = |M|² × phase space (QFT)
- Cross-section σ (Feynman diagrams)
- Branching ratios (수치)

213 의 자연 등장:
- Muon lifetime prefactor 192 = (NS²-1)(d²-1) atomic ★
- Z partial widths = 2·NS·NT atomic
- Higgs BR(H→bb) ≈ NS/d atomic

## 2. 213-native 등장

### 2.1 Decay = pair classification + phase
"교환" 부재.  AA/BB/AB pair 분류 + Lens layer transition.

### 2.2 Cross-section atomic
σ ∝ atomic geometric factor.

### 2.3 CP violation
δ_CP = 195° = 180 + 360/24 atomic (Phase 1).

## 3. 이미 깔린

- Generations.lean (N_gen = 3)
- ThetaQCD.lean (J·α^4 bound)
- NeutrinoMixing.lean (PMNS)
- CPViolation.lean
- ParticleLibrary (Phase 4)

## 4. Phase 진행 계획

### Phase PA — Decay rates ppm
μ, τ lifetime atomic.

### Phase PB — Hadron BR
B meson, K meson decay atomic.

### Phase PC — Cross-section
σ(e⁺e⁻ → hadrons), σ(pp → X) atomic.

### Phase PD — Higgs decays
BR(H→bb, ττ, γγ, gg) atomic.

### Phase PE — CP violation precise
ε, ε' atomic (Kaon system).

## 5. 다른 트랙 연결

- SM: gauge coupling
- Hadron: m_p, m_π
- 우주: η_B baryogenesis

## 6. 미해결

- B → s γ branching atomic
- K → πνν 정확
- Lepton universality atomic forced
