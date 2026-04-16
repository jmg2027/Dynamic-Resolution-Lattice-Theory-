# Cosmic Structure Sub-Project

> 우주 거대 구조 형성과 블랙홀 제트 — 심플렉스에서 은하까지.

## Scope
- 원시 밀도 요동 스펙트럼 (A_s, n_s, r)
- 물질 파워 스펙트럼 P(k) 및 σ₈
- BAO 음향 척도 (sound horizon)
- 구조 성장률 f(z)σ₈
- 우주 거미줄(cosmic web) 위상 구조
- 헤일로 질량 함수 (Press-Schechter)
- 커 블랙홀 (Gram matrix에서 회전)
- 블랙홀 제트 파워 (BZ mechanism)
- 제트 시준(collimation) 및 자기장 구조
- M-σ 관계 및 AGN 피드백
- 상대론적 제트 역학 (Lorentz factor)
- CMB 렌징 및 ISW 효과

## Key DRLT Inputs (0 free parameters)
```
d = 5,  n_S = 3,  n_T = 2,  c = 2
α_GUT = 6/(25π²) ≈ 0.02433
Ω_Λ = (1-1/π)(1+α_GUT/d) = 0.6850
Ω_m = 1 - Ω_Λ = 0.3150
Ω_b = Ω_m/(1 + d + 1/n_S) = 0.04898
DM/baryon = d + 1/n_S = 5.333
N_* = d²·n_T + d·n_S - d + 1 = 61
n_s = 1 - 2/N_* = 0.9672
r = 12/N_*² = 0.00323
A_s = α_GUT^n_S / (C(d²,n_S)·π) ≈ 1.99×10⁻⁹
w = -1 (exact)
Gravity-gauge split: 73%-27%
ℏ_h = A_h/(4ln2)  (dynamical Planck constant)
```

## Experiment Map
```
Part I: Large Scale Structure
CST_001: Primordial Power Spectrum — A_s, n_s, r from simplex inflation
CST_002: Matter Power Spectrum — P(k), σ₈, S₈ with DRLT parameters
CST_003: BAO Scale — sound horizon from DRLT Ω_b, Ω_m
CST_004: Growth Factor — f(z)σ₈ and γ from DRLT
CST_005: Cosmic Web Topology — void/filament from simplex network
CST_006: Halo Mass Function — Press-Schechter with DRLT σ₈, Ω_m

Part II: Black Hole Jets
CST_007: Kerr BH — spin from gauge sector holonomy
CST_008: Jet Power — BZ mechanism, max efficiency = gauge fraction
CST_009: Jet Collimation — magnetic pinch from holonomy structure
CST_010: M-σ Relation — BH-galaxy co-evolution from energy balance
CST_011: Relativistic Jet — Lorentz factor, synchrotron spectrum
CST_012: CMB Lensing & ISW — secondary anisotropies from DRLT
```

## Connections
- cosmology/: Ω_Λ, η_B, DM/baryon (background)
- quantum-gravity/: Regge action, BH entropy, Hawking T (gravity)
- critical-line/: spectral theory, ζ(2), Basel sum (mathematics)
- standard-model/: coupling constants (gauge sector)

## Status: ACTIVE
