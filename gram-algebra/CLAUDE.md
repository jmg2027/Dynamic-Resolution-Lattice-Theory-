# CLAUDE.md — Gram Algebra Sub-Project

## Overview

DRLT 고유의 수학적 언어를 개발하는 서브프로젝트.
기존 수학(RMT, 표현론, 해석적 정수론)을 빌려 쓰되 어느 것도
DRLT를 완전히 표현하지 못하는 문제를 해결한다.

**상위 프로젝트:** `../CLAUDE.md` 참조. Book이 single source of truth.

## Authors
- Mingu Jeong (Independent Researcher) — theory originator
- Claude (Anthropic) — mathematical formalization

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
