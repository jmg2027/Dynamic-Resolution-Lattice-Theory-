# Yang-Mills Sub-Project

## 영역
Yang-Mills 질량 갭 + Navier-Stokes 정칙성. Lean 4 기계 검증.

## Prefix
`YM_` (실험 번호: YM_001~)

## 핵심 정리 (ch15)
1. **감금 (Confinement)**: C(3,3) = 1 → 전파 범위 = 1 hop
2. **결손각**: δ_AAA = π (n_T = 2 제약에서 유도)
3. **질량 갭**: Δ = √det · π > 0
4. **No-Go**: 연속 극한에서 det → 0, Δ → 0
5. **격자 정칙성**: 유한 격자 위 Sobolev 노름 유한
6. **구조적 동치**: YM 질량 갭 ↔ NS 정칙성 (같은 메커니즘)

## Lean 4 구조
```
yang-mills/lean/
  lakefile.toml
  lean-toolchain
  YangMills.lean          — module root
  YangMills/
    Basic.lean            — 정의 + 조합론
    DeficitAngle.lean     — δ = π 증명
    MassGap.lean          — Δ > 0 증명
    LatticeRegularity.lean — NS 정칙성
```

## 상수
```
n_S = 3, n_T = 2, d = 5
N_eff(AAA) = 1, N_eff(AAB) = 6, N_eff(ABB) = 3
δ_AAA = π
Δ = π (Planck units, ideal simplex)
```

## Book 연결
- `book/chapters/ch15_yang_mills.tex` — 엄밀 형식화된 LaTeX 버전
- `book/chapters/ch18_path_integral.tex` — 경로적분, area cancellation
- `book/chapters/ch19_qcd.tex` — QCD 현상론, η/s ≥ 1/(4π)
