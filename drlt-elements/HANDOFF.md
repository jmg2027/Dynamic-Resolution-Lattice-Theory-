# DRLT 원론 — Session Handoff

## Branch
`claude/langlands-drlt-proofs-NPnSv`

## Status: PLANNED (2026-04-16)

## 위치: 로드맵 Step 1 (최하위 의존성, 최우선)

모든 후속 작업(Paper 1, 메타정리, Level 3)이 이것에 의존.

## 구현 순서

```
1. lakefile.toml        ← 5분
2. Entity.lean (~35줄)  ← 공리 + Eq 정의
3. Logic.lean  (~40줄)  ← True/False/And/Or/Exists
4. Nat.lean    (~40줄)  ← encode/decode + iso
5. Arithmetic.lean (~120줄) ← add/mul + comm/assoc ★핵심★
6. Order.lean  (~80줄)  ← le/lt + Decidable
7. Bridge.lean (~60줄)  ← import Init, DRLT.add=Nat.add
8. Compat.lean (~100줄) ← 기존 API 래핑 → Core.lean 연결
```

Phase 1 (1-6): `prelude`, 택틱 없음, term-mode only
Phase 2 (7-8): `import Init`, 택틱 해금, @[implemented_by]

## 기술 제약
- `prelude`에서 Eq 직접 정의 필요 (커널 미제공)
- `Nat`은 커널 빌트인 (zero, succ, rec 사용 가능)
- `@[implemented_by]`는 Bridge 이후에만
- 교환법칙 term 증명이 최대 난관 (~25줄)

## 완료 후
→ Step 2 (Paper 1): 기존 770정리를 Bridge 위로 재배치
→ Step 3 (Level 구조): 메타정리 기반 구축

## 스펙
`docs/spec.md` (~350줄) 참조
