# Foundations Sub-Project

> **수학-물리 브릿지 (Derivation Chain).**
> 공리(관계)에서 물리 법칙으로 이어지는 대수적 뼈대.
> `관계 → ℂ (Frobenius) → d=5 (atomic) → Gram → W,φ → rank cascade → 물리`.
> 순수 수학도 순수 물리도 아닌, 둘을 잇는 구조의 공간.
> "Algebraic Priority": 결과는 세기(counting)에서 나옴 — 조합·대수·기하 방법으로 물리 유도.

## Scope

### 기본 (FND_001–010, STABLE)
- 왜 ℂ인가 (Frobenius)
- 왜 d=5인가 (chiral atomic decomposition)
- (3,2) uniqueness, SU(5) emergence
- 변분 정리: δ=π, det=2/3, c=2
- Occupation fraction spectrum (10 values, 206 states)
- Trace conservation (Σ Δ_i = 0)

### Session B 확장 (FND_011–033, 수학 backbone)
- Grassmannian Gr(3,5) / FM cohomology (FND_011, 020)
- Binet–Cauchy 채널 분해 1+12+12=25 (ch08 대응)
- Tensor fractal tower, Schur–Weyl (FND_017)
- Regge action + 4-sector framework (FND_018, 019, 024–029)
- Church–Rosser confluence ⟺ scale-invariance (FND_030–033)
- n=5 unique alive decomposition, ∀v≥6 ambiguity

## Experiments (P=순수물리, M=순수수학, B=브릿지)

### Core (FND_001–010, STABLE)
```
FND_001: B — Variational ∂(Δ⁵) δS/δψ=0
FND_002: B — Hinge-opposite duality → 3+1 spacetime (12/12 ✓)
FND_003: B — Definitive variational (8/8 ✓)
FND_004: B — Symmetric variational w,θ 최적화 (8/8 ✓)
FND_005: M — Rank cascade random matrix
FND_006: B — Theorem 3 δ²S<0 + det(SST) 해석 (7/7 ✓)
FND_007: B — Temporal fraction / Higgs 질량 개선 (7/7 ✓)
FND_008: M — Combinatorial census f_occ 완전 열거
FND_009: M — Unidentified f_occ 미사용값 탐색
FND_010: B — SU(5) emergence from f_occ 스펙트럼
```

### Session B 확장 (FND_011–033, 수학 backbone / 브릿지 탐색)
```
FND_011: M — FM cohomology Gr(3,5), χ=5^N·(N+1)!
FND_012: M — Swap involution Grassmannian 형식화
FND_013: B — 2.4% = α_GUT 가설 (★ REFUTED: 체리픽)
FND_014: B — FND_013 audit / two-route consistency
FND_015: B — ε₀ = α/(2π) derivation (OPEN)
FND_016: B — Geometric det(G_h) 직접 계산
FND_017: M — Tensor fractal tower (Schur–Weyl)
FND_018: B — Regge action boundary
FND_019: B — Variational Regge extremum (★ REFUTED: 1-param family)
FND_020: M — Level functor (Plücker + FM)
FND_021: B — w*=3/(5π) 정밀 (★ REFUTED: 0.4% gap)
FND_022: M — N_eff 기하학적 설명
FND_023: M — Simplex contacts codim 가시성
FND_024: B — 4-sector framework 형식화
FND_025: B — Gravity location Λ^k(C⁵) (★ REFUTED)
FND_026: B — Gravity as shape deficit (★ REFUTED: shape-only)
FND_027: B — Einstein analog formalization
FND_028: B — Einstein frame 8-check (6/8 informative fails)
FND_029: B — Layered frame gravity/SM (5/16 AAB)
FND_030: M — Swap confluence (a,b) Church–Rosser
FND_031: M — Refinement operators 고정점 → 4-simplex
FND_032: M — Claim 2': scale-invariance ⟺ confluence
FND_033: M — γ' operator forces 4D (unique-decomp)
FND_034: B — ε₀ = α_GUT/(2π) (★ REFUTED: 2.6% gap)
FND_035: B — M_i direct geometric (★ REFUTED)
FND_036: B — Regge deficit M_i (★ REFUTED)
FND_037: M — W3 Schubert T-weight (★ REFUTED)
FND_038: M — Swap tower = 유한 반복 고정점 (12/12 ✓, Lean 17 thm)
FND_039: M — Tower atom-dependency scope (4/4 ✓, atom-INDEP)
```

## Related Papers (root papers/)
```
paper1_chiral_decomposition.tex  — Why ℂ, why d=5
paper2_frobenius_to_gauge.tex    — Frobenius → gauge group
```

## Book Chapters
Part I (ch01-03): Foundations
Part II (ch04-05): Simplex geometry + variational theorems
ch21: Occupation fraction + Higgs quartic

## Key Theorems
1. Frobenius: ℝ, ℂ, ℍ → only ℂ gives chiral d=5
2. Atomic decomposition: d=5 unique for N≥6 vertices
3. δ(AAA) = π (exact, from variational)
4. c = 2 (temporal density from n_T/n_S volume)
5. f_occ spectrum: 10 distinct values, 206 total states
6. SU(5) → SU(3)×SU(2)×U(1) from ∧ᵏ(ℂ⁵) branching
7. Gr(3,5) Schubert cell count = 10; FM χ = 5^N·(N+1)! (N=1..5)
8. (n_A, n_B)=(3,2) 채널 분해 1+12+12=25 (Binet–Cauchy)
9. Scale-invariance ⟺ confluence (FND_032)
10. n=5 unique alive decomposition; ∀v≥6 ambiguity

## Lean 형식화 (수학 트랙 소속)
Session B의 5개 Lean 파일은 `critical-line/lean/PmfRh/`에 있음:
ScaleInvariantFoundation, DimensionBridge, BinetCauchy, ScaleConfluence, GrassmannianData.
이들은 수학 트랙에서 관리. foundations/에는 해당 FND 실험 파이썬 파일만 존재.

## 상세 문서
- `notes/FORMAL_FOUNDATION.md` — FND DAG + 의존성 + 진행 상태
- `notes/GAPS_REGISTER.md` — 26개 열린 문제 (G-D2, G-D3, G-D6 등)
- `theory/scale_invariant_foundation.tex` — d=5 + 4D + scale-invariance LaTeX
- `theory/chiral_vs_trivial.md` — Gram eigenvalue I/II/III 표현론
