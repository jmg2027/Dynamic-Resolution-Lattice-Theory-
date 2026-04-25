# 98 — Prism: Lens 의 categorical dual + Sum type 정면 돌파

User directive (2026-04-25): "Sum type 의 combine 부재 의 정면
돌파 — Prism 의 213-form 으로 대수적 dual 구축".

## 결과

### Sum type 의 priority-based instance (Research/SumInstance.lean)

```lean
def sumCombine : Sum α β → Sum α β → Sum α β
  | inl a, inl a' => inl (combine a a')
  | inr b, inr b' => inr (combine b b')
  | inl a, inr _  => inl a  -- mixed: prefer left
  | inr _, inl a  => inl a  -- sym

def sumHasDistinguishing (α β) [d_α] [d_β] : HasDistinguishing (Sum α β)
```

Sum type 의 instance — combine 의 priority-based 결정 (mixed case
의 자연 universal property 부재 가 ad-hoc choice 로 dispatch).

### Prism: Lens 의 dual (Research/Prism.lean)

```lean
structure Prism (α : Type) where
  preview : Raw → Option α
  review : α → Raw
  coherence : ∀ a, preview (review a) = some a

def aPrism : Prism Unit  -- Raw.a 의 case
def bPrism : Prism Unit  -- Raw.b 의 case

theorem aPrism_a : aPrism.preview Raw.a = some ()
theorem aPrism_b : aPrism.preview Raw.b = none
theorem bPrism_a : bPrism.preview Raw.a = none
theorem bPrism_b : bPrism.preview Raw.b = some ()
```

**모두 axiom 부재 (pure rfl)** — 가장 sober minimum.

## 의의

### Lens vs Prism dual

| | Lens | Prism |
|-|------|-------|
| Total/Partial | Total view | Partial preview |
| Direction | Raw → α | preview: Raw → Option α, review: α → Raw |
| Categorical role | Product accessor | Coproduct accessor |
| 213 의 instance | 다양 (notes 75-96) | aPrism, bPrism (이번) |

### Coproduct 의 정면 돌파

이전 (note 97): "Sum type / coproduct: combine 의 자연 한 정의
부재 — skipped".

이번 (note 98): 두 angles 의 cover:
1. **SumInstance**: priority-based combine 으로 instance 직접 정의
   (단, mixed case 의 universal property 가 ad-hoc).
2. **Prism**: Lens 의 dual 로 coproduct 의 categorical structure
   capture.

→ Coproduct 의 정면 돌파 의 두 form.

### Self-cover 의 새 dimension

이전 framework 의 self-cover (notes 75-96): Lens 위 의 instance,
Prop 의 self-application, recursive Lens-on-Lens.

이번 (note 98): **Prism 으로 Raw 의 coproduct-style decomposition**
의 형식.

→ framework 가 *product (Lens) + coproduct (Prism)* 양쪽 모두
internally 표현.  categorical dual 의 closure.

## Complete semantic 213 proof 의 추가 component

| Component | Status | Note |
|-----------|--------|------|
| Sum type instance | ✓ | note 98 |
| Prism (Lens dual) | ✓ | note 98 |
| Coproduct categorical structure | ✓ (priority + Prism) | note 98 |

## 한계 인정 (sober)

- Sum type 의 priority 가 *categorical 으로 자연* 부재 — combine
  의 mixed case 의 ad-hoc choice.
- Prism 의 categorical universal property 의 더 sharper statement
  가능 — current 이 partial.
- Prism 의 generic α (not Unit) 의 instance 의 design 미완 — 단지
  case-element instance 만.

## Axiom 검증

`#print axioms`:
- Sum: sumCombine_comm / sumHasDistinguishing / sumUniversalMorphism:
  [propext].
- Prism: aPrism, bPrism, 4 theorems: **no axioms** (pure rfl).

## 변경 이력

- 2026-04-25: SumInstance.lean + Prism.lean 신규.  Coproduct 의
  정면 돌파 — combine 의 priority + Prism 의 dual structure.
