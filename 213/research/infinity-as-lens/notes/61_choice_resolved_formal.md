# 61 — "선택 = Lens specification" 의 formal demonstration

## 결과

`Research/ChoiceResolved.lean`:

**`choice_as_lens_spec`**: 임의 slash-congruence E 에 대해
concrete Lens 존재 — Classical.choice 부재 하 universal
construction.

```
∀ E : Raw → Raw → Prop, (equivalence + slash-cong) →
  ∃ L : Lens (Raw → Prop), ∀ r r', L.view r = L.view r' ↔ E r r'
```

증명: ⟨universalLens E, universalLens_kernel_eq_E E ...⟩.

## 의의

Note 44 의 "선택 = Lens specification" thesis 의 명시 적 형식
demonstration.

추상 적 choice axiom 사용 안 함.  대신 universalLens E 라는
**explicit named witness** 으로 existential 구체화.

## Axiom 검증

```
#print axioms choice_as_lens_spec
-- [propext, Quot.sound]
```

External axiom 0.  Classical.choice 부재.  Lean 4 core 만.

## "Choice" 의 213 reduce

전통 적 frame:
- "각 nonempty set 에서 element 선택 함수" → Choice axiom 필요.

213 frame:
- 각 slash-cong E 에 대해 Lens spec 명시 → 명시 적 universalLens E.
- 추상 적 choice 부재.  매번 explicit specification.

이게 note 44 의 의미: **모든 추상 "선택" 이 213 안 에서는
명시 적 Lens spec**.  Choice 가 mystery 가 아니라 spec 작성.

## 다른 ZFC axiom 들 도?

이 패턴 의 일반화:
- Pairing: prodLens 로 reduce.
- Power set: Cantor diagonal (Σ5) 로 reduce.
- Replacement: Lens spec 으로 image 명시.
- Foundation: Raw 가 well-founded inductive type (Lean built-in).
- Infinity: Σ3 (ℕ → Raw injective) 로 reduce.

각 ZFC axiom 이 213 위 specific demonstration 으로 환원 가능.

## 변경 이력

- 2026-04-25: Choice 의 213 reduce formal.  universalLens 가
  explicit witness.
