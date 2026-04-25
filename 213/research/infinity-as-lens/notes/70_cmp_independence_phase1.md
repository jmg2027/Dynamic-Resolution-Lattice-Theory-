# 70 — cmp-independence Phase 1: foundational layer

`IMPLEMENTATION.md §5` 의 cmp-independence meta-theorem 의 첫
형식 step.

## 결과 (Research/CmpIndependence.lean)

### CmpProps 추상화

```
structure CmpProps (cmp : Tree → Tree → Ordering) : Prop where
  eq_iff : ∀ x y, cmp x y = .eq ↔ x = y
  swap : ∀ x y, cmp x y = (cmp y x).swap
```

이 두 properties 만으로 cmp 의 well-behavedness 정의.  Tree.cmp
의 specific lex 구조 부재.

### 정리

- `Tree_cmp_props`: Tree.cmp 가 CmpProps 만족.
- `cmpRev_props`: cmpRev cmp 도 CmpProps 만족 (involutive).
- `canonicalBy cmp` / `RawBy cmp`: cmp-parametric Raw 정의.
- `canonicalBy_Tree_cmp`: 원래 Raw 와 일치.

### Axiom 검증

`#print axioms`:
- Tree_cmp_props: [propext]
- cmpRev_props: no axioms
- canonicalBy_Tree_cmp: no axioms

Classical.choice 부재.  AXIOM §5.2.1 falsifiability 유지.

## 의의

이 Phase 1 결과 가 보이는 것:

1. **Tree.cmp 의 lex 구조 가 axiom-irrelevant**: CmpProps abstract
   level 에서 Raw 의 정의 가 작동.  Tree.cmp 가 만족 하는 specific
   lex 알고리즘 은 implementation choice.

2. **cmp 선택 의 자유 도**: cmpRev (또는 다른 CmpProps-만족 cmp)
   도 RawBy 로 valid Raw analog 정의.  여러 cmp 가 같은 framework
   에 fit.

3. **Internal access 정당화**: 이 파일 이 encoding artifact 의
   metalevel 검증 — internal 을 들여다 보는 것 이 정당.

## Phase 2 (future work)

**Bijection RawBy cmp1 ≃ RawBy cmp2** — 두 cmp choices 가 type-
level isomorphism 갖음.

이는 specific cmp 의 lex 구조 가 일반 적 으로 부재 하므로 더 깊은
도구 (slash-comm equivalence, canonicalize function, mirror 등)
필요.

Tree.cmp + cmpRev specific case 는 mirror 로 demonstrable 하지만
일반 cmp 사이 의 bijection 은 case-by-case.

## IMPLEMENTATION.md 업데이트

§5 의 "현재 상태: 형식화 없음" 가 Phase 1 완료 후 "foundational
layer 형식화 ✓, bijection 미완" 로 갱신 가능.

## 변경 이력

- 2026-04-26: cmp-independence Phase 1.  CmpProps 추상화 +
  Tree.cmp / cmpRev 가 만족 + canonicalBy/RawBy parametric +
  원래 Raw 와의 일치.
