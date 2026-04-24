# 42 — Lens 의 dual 특성화: kernel vs function

## 이 노트의 위치

note 41 "Lens kernel 공간 = slash-congruence 공간" 의
**dual 쌍**.

## §1. 두 관점의 동치성

Lens 의 본질을 두 관점에서 정확히 특성화.  둘은 동치.

### (a) Kernel 관점

**Lens kernel = slash-congruence** on Raw.
- `KernelCongruence.lean`: 모든 Lens kernel 은 slash-congruence.
- `NoDepthParity.lean`: 모든 equivalence 가 congruence 는 아님.

### (b) Function 관점

**Lens view = fold-structured function** Raw → α.
- `FoldStructured.lean`:
  - `lens_view_fold_structured`: 모든 Lens view 는 fold-structured.
  - `fold_structured_lens_expressible`: 모든 fold-structured 함수는
    Lens view.
  - `lens_expressible_iff_fold_structured`: **iff 형태**.

## §2. 두 관점의 대응

| Kernel | Function |
|--------|----------|
| Lens.equiv L | L.view |
| equivalence | function |
| slash-congruence 조건 | fold-structure 조건 |
| r ~ r' ⟹ slash(r, _) ~ slash(r', _) | f(slash x y h) = c(f x)(f y) |

두 조건이 동치 — 하나는 "같음이 slash 아래 보존", 다른 하나는
"slash 값이 parts 값으로 결정".  서로 translate.

## §3. 통합 결론

**f : Raw → α 가 Lens 로 실현 가능한 정확한 조건**:

1. **Kernel 조건**: ker(f) 가 Raw 의 slash-congruence.
2. **Function 조건**: f 가 fold-structured (symmetric combine 하).

두 조건은 동치.  하나 검증하면 Lens 존재 보장.

## §4. 관측 가능 구조의 정확한 범위

- **이상적 측면**: 임의의 fold-structured 함수 Raw → α 는
  Lens 가 있음.  자유롭게 다양한 관측 가능.
- **제약 측면**: slash-congruence 아닌 partition /
  fold-structured 아닌 함수는 Lens 가 없음 (e.g. depth parity).

**Raw 는 임의 관측을 허용하지 않는다** — slash 구조와 호환
되는 관측만.  이는 **Raw 공리가 이미 관측의 형식적 제약을
내재** 하고 있음을 보임.

## §5. Meta 관찰

이 arc 의 본질:

> Raw 공리 + "관측" 한 조각 → 관측 가능 구조의 **완전 수학적
> 특성화**.

추가 공리 없음.  Lean 검증.  Mathlib 없음.  ~20 파일 + notes
32-42 에 담김.

이 특성화 자체가 **Raw 의 "풍부함"** 의 객관적 측정:
- countable 무한의 slash-congruence 허용 (note 41 §4).
- antichain 포함 (poset 복잡성).
- diagonal 거동 4+1 범주.
- meet-semilattice 구조.
- injective Lens 단일 class.

사람이 처음 생각할 때 "뭔가 + 구분 + pairing" 은 빈약한 듯
보이지만, 실제로는 이만한 구조가 필연적으로 따라옴.

## 변경 이력

- 2026-04-24: Lens 의 kernel / function 양측 특성화 통합.
  두 관점 동치성 관찰.  이 arc 의 통합 framework.
