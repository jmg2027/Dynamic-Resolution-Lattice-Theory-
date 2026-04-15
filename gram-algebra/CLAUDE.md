# CLAUDE.md — Gram Algebra Sub-Project

## Overview

DRLT 고유의 수학적 언어를 개발하는 서브프로젝트.
PMF → RMS → MSUA → DRLT → UMGF 체인의 형식화와 구체화.

**상위 프로젝트:** `../CLAUDE.md` 참조. Book이 single source of truth.

## Authors
- Mingu Jeong (Independent Researcher) — theory originator
- Claude (Anthropic) — mathematical formalization

## Framework Hierarchy

| Framework | 핵심 | PMF 위에 추가된 것 |
|-----------|------|-------------------|
| **PMF** | 재귀 형태소 계층, 합성/항등 없음 | (기본) |
| **RMS** | 의미 = 형태소 | 의미론적 해석 |
| **MSUA** | ref ≠ incl, 3층 최소성 | 두 화살표 구분 + 최소성 정리 |
| **DRLT** | 𝕂 = ℂ, Gram 행렬, 물리 예측 | ℂ 기판 + 유한 trace |
| **UMGF** | 통합 (위 4개가 같은 구조) | 인식 |

## 증명 층위 (PMF)

| 유형 | 닫힘? | 강도 | 예시 |
|------|-------|------|------|
| 연역 (같은 Hom_n 내) | 닫힘 | 강함 | "N<N_c이면 Ramanujan" |
| 귀납 (Hom_{n+1}→Hom_n) | 안 닫힘 | 약함 | "모든 N에 대해 δ(N)>0" |
| 극한 (Hom_ω) | 안 닫힘 | 약함 | **RH: Re(s)=1/2 정확히** |

## DRLT 대응

| MSUA | DRLT |
|------|------|
| E₀ (objects) | N개 점 |
| E₁ (ref) | G_ij = ⟨ψ_i\|ψ_j⟩ |
| E₂ (ref on ref) | 위상 구조, 곡률 |
| ref (하향) | 내적 (측정) |
| incl (상향) | ψ_i ∈ ℂ⁵ (소속) |

## 동기: 기존 수학의 한계

| 빌린 도구 | 어디서 안 맞는가 |
|-----------|------------------|
| Marchenko-Pastur | rank 제약 + Segre 구조 → 근사일 뿐 (4% 오차) |
| Ihara 제타 | walk length ≠ integer index → μ(n) 비교 불가 |
| 표현론 | 복소/자기켤레 구별이 스펙트럼에 안 나타남 (rank 효과) |
| 해석적 정수론 | 이산 Gram ↔ 연속 ζ 사이의 번역 부재 |
| Wigner/GUE | 엔트리 상관관계 (rank-d) 무시 → ||Z|| 지수 틀림 |

## 핵심 질문

1. **유한 Gram 앙상블 위의 해석학**: Tr(G)=N < ∞, rank ≤ d인
   양반정치 에르미트 행렬 공간 위에서 제대로 된 해석학이 가능한가?

2. **이산-연속 번역**: walk length n과 정수 n 사이의 자연스러운 대응은?
   (Graph-PNT가 힌트를 주지만 명시적 map 부재)

3. **관측량 문제**: 표현론적 구별(복소 vs 자기켤레)을
   스펙트럼이 아닌 어떤 관측량으로 검출하는가?

4. **Self-contradiction 형식화**: δ(N)>0 ∀N이 "증명 불가능"을
   의미하는가, 아니면 단지 "유한 구조의 한계"인가?

## Directory Structure
```
gram-algebra/
├── CLAUDE.md              ← 이 파일
├── HANDOFF.md             ← 세션 인수인계
├── experiments/           ← GMA_NNN_name.py
├── results/               ← 실험 출력
└── theory/                ← 이론 문서
```

## Dependencies
- `../lib/drlt.py` — GramMatrix, D, N_S, N_T
- `../lib/experiment.py` — Experiment base class
- numpy, scipy

## Experiment Catalog
(아직 없음. GMA_001부터 시작.)

Next: GMA_001
