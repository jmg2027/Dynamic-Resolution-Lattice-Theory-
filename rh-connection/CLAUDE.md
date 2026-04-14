# CLAUDE.md — RH Connection Sub-Project

## Overview
DRLT에서 리만 가설(RH)로의 연결을 형식화하는 독립 서브프로젝트.

**핵심 체인:** ℂ unique → β=2 → GUE → d=5 → ζ(2) → s=2 → RH

**상위 프로젝트:** `../CLAUDE.md` 참조. Book이 single source of truth.

## Authors
- Mingu Jeong (Independent Researcher) — theory originator
- Claude (Anthropic) — mathematical formalization, numerical experiments

## Directory Structure
```
rh-connection/
├── CLAUDE.md              ← 이 파일
├── lib/
│   └── rh_core.py         ← 핵심 라이브러리 (GUE 도구, Z_N 정의, 스펙트럼 분석)
├── experiments/
│   └── EXP_071_*.py       ← 수치 실험 (experiment.py 상속)
├── theory/
│   ├── self_contradiction.tex  ← 자기모순 경계 정리 (형식화)
│   └── z_n_definition.tex      ← Z_N(s) 형식적 정의
├── results/
│   └── EXP_071_*.txt      ← 실험 결과
└── figures/
    └── *.png              ← 생성된 그래프
```

## Dependencies
- `../lib/drlt.py` — GramMatrix, D, N_S, N_T, ALPHA_GUT, ZETA_2
- `../lib/experiment.py` — Experiment base class
- numpy, scipy

## The Derivation Chain (Status)

| Step | Statement | Status |
|------|-----------|--------|
| 1 | ℂ is the unique substrate (Frobenius) | **Theorem** (Paper 2) |
| 2 | ℂ → β=2 → GUE (Dyson class) | **Theorem** (Mehta) |
| 3 | d=5, ℂ⁵ = ℂ² ⊕ ℂ³ unique | **Theorem** (Paper 1) |
| 4 | s = rank(G^AA) − 1 = 2 | **Theorem** (EXP_067) |
| 5 | Propagator D(n) = 1/n² → ζ(2) | **Theorem** (ch08) |
| 6 | GUE pair correlation = ζ zero spacing | **Conjecture** (Montgomery-Odlyzko) |
| 7 | Re(s) = 1/2 from self-contradiction boundary | **To formalize** |

## Key Definitions

### Z_N(s) — Gram Spectral Zeta Function
For N vertices ψ_i ∈ ℂ⁵, W-graph Laplacian L with eigenvalues μ_k:
```
Z_N(s) = Σ_{k=1}^{N-1} μ_k^{-s}   (Re(s) > d_s/2)
```

### Self-Contradiction Boundary
δ(N) > 0 for all finite N. δ→0 requires N→∞ which violates Tr(G)=N<∞.

### β=2 Level Repulsion
P(s) ∝ s^β at small s. β=2 (quadratic) from ℂ, not β=1 (linear, GOE).

## Experiment Catalog
- EXP_071: β=2 level repulsion, GUE pair correlation, spectral gap scaling,
  self-contradiction boundary, near-Ramanujan property, complete chain

## Running Experiments
```bash
cd rh-connection/experiments && python EXP_071_rh_chain.py
```

## What DRLT Adds to the RH Landscape
1. **WHY GUE**: ℂ uniqueness forces β=2. Previously empirical mystery.
2. **WHY s=2**: ℂ² sector dimension. Not assumed, derived.
3. **Finite framework**: δ(N) = O(1/√N) > 0. RH as limit theorem.
4. **Self-contradiction**: exact Re(s)=1/2 at the boundary where the framework contradicts itself.

## Open Problems (This Sub-Project)
1. Z_N(s) → ζ(s) in what limit? (continuum limit problem)
2. Montgomery pair correlation from "why GUE" direction
3. n_B/n_A = 2/3 derivation from Binet-Cauchy
4. Rigorous δ(N) = Θ(1/√N) bound for Gram ensemble

## Workflow
1. Theory in `theory/*.tex` — small LaTeX documents
2. Experiments in `experiments/EXP_071_*.py`
3. Results auto-saved to `results/`
4. When mature, consolidate into `../book/chapters/ch21_riemann.tex`
