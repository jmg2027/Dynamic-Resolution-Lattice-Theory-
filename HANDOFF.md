# Session Handoff — 2026-04-18 (cont.)

## Branch
`claude/continue-handoff-213-fC38X` (로컬. 아직 push 안 함.)
이전 base: `claude/integrate-langlands-drlt-proofs-R2I9d` (PR #22 merged).

## What Was Done This Session

### Priority 1 완료: Reachable 위의 정리들
- 새 파일: `213/framework/E213/Firmware/Reachable.lean` (129줄).
- E213.lean에 import 추가.
- ARCHITECTURE.md 성질 섹션 갱신.

### 증명된 것 (0 sorry)
1. **`Raw.wellFormed`**: 구문적 well-formed 판정.
   - atom 이면 True.
   - rel x y 이면 x ≠ y ∧ 재귀.
2. **특성화**: `Reachable x ↔ Raw.wellFormed x`.
   - `reachable_of_wellFormed`: wellFormed → Reachable (Raw 재귀).
   - `wellFormed_of_reachable`: Reachable → wellFormed (Reachable 귀납).
3. **판정 가능**: `instance : DecidablePred Reachable`.
4. **유령 없음**: `no_self_rel_reachable: ¬ Reachable (rel x x)`.
5. **필연 ≠**: `reachable_rel_ne: Reachable (rel x y) → x ≠ y`.
6. **부분구조 닫힘**: `reachable_left`, `reachable_right`.
7. **slash 닫힘**: `reachable_slash` = `Reachable.step`.

### 계산 확인 (decide)
- `Reachable ab₀`, `Reachable aab₀` — True.
- `¬ Reachable (rel a₀ a₀)`, `¬ Reachable (rel ab₀ ab₀)` — True.

### Level 열거
- `expandOne : List Raw → List Raw`: 서로 다른 쌍에 slash 적용.
- `levelUpTo : Nat → List Raw`: 3 atom seed에서 n단계 자연 전개.
- Level 0: 3개 (atoms).
- Level 1: 9개 (3 atoms + 6 ordered rels).
- 주의: ARCHITECTURE.md의 "3, 5, 12"는 2 atom seed 기준. 다른 초기조건.

### 빌드
- `lake build` 성공. 3파일 모두 clean.

## 파일 구조
```
213/framework/
├── E213.lean                       ← import 3줄
├── E213/Firmware/RawAxiomV3.lean   ← SSOT. 공리. (112줄)
├── E213/Firmware/Properties.lean   ← 9 성질. (127줄)
├── E213/Firmware/Reachable.lean    ← ★신규. 특성화+판정+열거. (129줄)
├── lakefile.toml
└── lean-toolchain
213/ARCHITECTURE.md                 ← v3 아키텍처 (성질 섹션 갱신)
213/CORE.md                         ← 213의 본질 (변경 없음)
```

## Open Problems (Priority)

### 1. ~~Reachable 위의 정리들~~ ✓ 이번 세션에 완료.
Level n 카운트 공식은 미증명. levelUpTo로 계산은 가능.
- |levelUpTo 0| = 3, |levelUpTo 1| = 9. Level 2 이상 decide 미확인.

### 2. Hypervisor 재구축 (미착수)
v3 위에 `==` (isTrivial) 정의. 등호의 세 성질 증명.
PA, 집합론을 v3 위에 올리기.

### 3. 이전 발견의 v3 재형식화 (미착수)
(alg, chain) 좌표, 증명 모양, 비용 예측을 v3 위에서 다시.

### 4. 자연 전개 자동화 (부분 완료)
levelUpTo 구현됨. 남은 것:
- Level 2, 3의 정확한 count.
- 성장 패턴 공식 (2 atoms vs 3 atoms seed).
- `expandOne_preserves_reachable` 증명.

## Unresolved from This Session
- `levelUpTo 2` decide 비용 미확인.
- ARCHITECTURE.md "3,5,12" 수열은 2 atoms seed. 구현은 3 atoms.

## Next Steps (제안)
1. `expandOne_preserves_reachable`: Reachable 보존 증명.
2. levelUpTo count 공식 증명.
3. Hypervisor 시작: isTrivial, equivalence 정의.

## File Map
```
213/framework/E213/Firmware/Reachable.lean  ← 신규 (129줄)
213/framework/E213.lean                     ← import 추가
213/ARCHITECTURE.md                         ← 성질 섹션 갱신
```

## Key Insight
`/` 하나. `a/a` 불가. `Reachable`만 존재.
이번 세션: Reachable이 **판정 가능**. "진짜 존재"가 계산 문제가 됨.
