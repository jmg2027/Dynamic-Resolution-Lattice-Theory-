# CLAUDE.md — DRLT Elements (원론)

## 목표
**단일 공리(Entity.point)에서 출발하여 모든 수학을 따름정리로 유도하는 Lean 4 형식 체계.**

유클리드 원론의 현대판: 점 → 논리 → 산술 → 대수 → 기존 770정리 전부.

## 핵심 원칙
1. **Phase 1 파일은 `prelude`**: Init 없이 커널만 사용
2. **택틱 금지** (Phase 1): term-mode 증명만
3. **Bridge 이후 자유**: import Init → 택틱, @[implemented_by] 해금
4. **기존 코드 보존**: critical-line/lean/ 코드를 Bridge 위로 이전

## 디렉토리 구조
```
drlt-elements/
├── CLAUDE.md         ← 이 파일
├── HANDOFF.md        ← 세션 인수인계
├── lean/
│   ├── lakefile.toml
│   ├── DRLT/
│   │   ├── Entity.lean       ← Phase 1-1: THE AXIOM
│   │   ├── Logic.lean        ← Phase 1-2: Eq, And, Or
│   │   ├── Nat.lean          ← Phase 1-3: 자연수 유도
│   │   ├── Arithmetic.lean   ← Phase 1-4: +, ×, 성질
│   │   ├── Order.lean        ← Phase 1-5: ≤, <, 결정가능성
│   │   ├── Bridge.lean       ← Phase 2-1: import Init, iso
│   │   └── Compat.lean       ← Phase 2-2: 기존 코드 호환층
│   └── DRLT.lean             ← root import
└── docs/
    └── spec.md       ← 상세 스펙 문서
```

## Authors
- Mingu Jeong (Independent Researcher) — theory originator
- Claude (Anthropic) — formalization
