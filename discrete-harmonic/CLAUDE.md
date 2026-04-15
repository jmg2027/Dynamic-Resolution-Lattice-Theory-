# Discrete Harmonic Analysis (DHA) Sub-Project

> **심플렉스 위의 이산 조화해석학 — 새 수학 분야.**
> cos/arccos를 유한 구조로 완전 대체하여 DRLT의 초월성을 제거.
> "π는 공리가 아니라 유한 합의 극한이다."

## Prefix: DHA

## Core Problem

DRLT의 Regge action에서 **cos/arccos가 유일한 초월 함수**:
```
cos(F(x)) = -x/(1-2x),  F = algebraic
S(ε,N) = ... arccos(ε/√(1-2ε²)) ...
```

**질문**: 유한 심플렉스(d=5, N_eff=9)에서 cos를 대수적으로 대체할 수 있는가?

## Key Ideas

### 1. Chebyshev Basis (기존 결과)
```
T_n(cos θ) = cos(nθ)  →  arccos 제거
S_Cheby[G] = Σ_h √det(G_h) · Σ_{n=1}^{N_eff} (1-T_n(cos θ_h))/n²
```
Lean 형식화 완료 (ChebyshevAction.lean, 0 sorry).

### 2. Finite Spectral Measure
```
ζ_N = Σ_{n=1}^N 1/n²  replaces  ζ(2) = π²/6
N = 9 = C(5,3)-1 = non-SSS channels
```
ζ₉ → α₉: 0.001% (vs ζ(∞) → α_GUT: 0.1%)

### 3. Combinatorial Laplacian
∂(Δ⁵) 위의 조합론적 Laplacian Δ_k.
고유값 스펙트럼 → 이산 조화함수 기저.

### 4. S₅ Character Theory
S₅ has 7 irreps: (5), (4,1), (3,2), (3,1,1), (2,2,1), (2,1,1,1), (1,1,1,1,1).
각 irrep의 character → 심플렉스 위 함수의 자연적 기저.

### 5. Pontryagin Duality (Finite)
유한 아벨 군의 자기 쌍대성 → 정확한 스펙트럼 분해.
연속 cos의 "주기 2π" → 이산 주기 √(24ζ_N).

## Mathematical Goals
1. ∂(Δ⁵) Laplacian 고유값 완전 분류
2. Regge action을 character expansion으로 분해
3. α_GUT = 1/(d² · ζ_N) 공식의 스펙트럼 해석
4. cos-free Regge calculus의 엄밀 정의
5. 0.001% 잔차의 정확한 스펙트럼 기원

## Key Constants
```
d = 5, N_S = 3, N_T = 2, c = 2
N_eff = 9 = C(5,3)-1
|S₅| = 120
dim ∂(Δ⁵): vertices=5, edges=10, faces=10, tetra=5
ζ₉ = Σ_{n=1}^9 1/n² ≈ 1.53977
ζ(2) = π²/6 ≈ 1.64493
α_GUT = 6/(25π²) ≈ 0.02432
α₉ = 1/(25ζ₉) ≈ 0.02598
```

## Experiment Map
```
DHA_001: Combinatorial Laplacian eigenvalues on ∂(Δ⁵)
DHA_002: S₅ character decomposition of dihedral angles
DHA_003: Finite Fourier transform — cos_N vs √(24ζ_N)
DHA_004: Algebraic Regge action (arccos-free)
DHA_005: Spectral zeta function ζ_Δ(s)
```

## References
- yang-mills/lean/YangMills/ChebyshevAction.lean
- critical-line/experiments/RH_040_chebyshev_action.py
- atoms/experiments/ATM_029-031
- atoms/theory/complete_theory.md §10-11
- book/chapters/ch04_simplex_geometry.tex
- book/chapters/ch15_yang_mills.tex
