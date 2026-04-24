# 36 — Identity Lens + Yoneda-dual (Q34.3, Q34.4 의 부분 답)

## Q34.4 재해석

원래 질문: "`Lens.fromRaw r : Lens α` 같은 map 이 자연스러운가?"

답: **canonical 한 self-encoding 은 없음**.  Lens α 는 α 에
의존적이므로 Raw 원소 하나로 "모든 α 에 대한 Lens" 를 만들
수 없다 (α 의 data 가 필요).

**하지만 dual 이 자연스러움**.

## §1. Yoneda-dual

`L.view : Raw → α` 을 L 에 대해 curry 하면:

```
Raw.eval : Raw → (∀ α, Lens α → α)
Raw.eval r α L := L.view r
```

각 Raw 원소는 **"모든 Lens 를 평가하는 함수"**.  Lens.view
의 "시점" 을 Raw 쪽에서 본 형태.

## §2. Identity Lens (Q34.3 가장 단순한 구현)

`Research/IdentityLens.lean`:

```
def idLens : Lens Raw where
  base_a := Raw.a
  base_b := Raw.b
  combine x y := if h : x ≠ y then Raw.slash x y h else Raw.a
```

diagonal 에서 fallback Raw.a 사용.  slash 분기는 `x ≠ y`
보장되므로 fallback 은 view 계산 중 **절대 hit 되지 않음**.

정리 `idLens_is_id : idLens.view r = r` 로 view = identity
on Raw 기계 검증.

이는 Q34.3 의 최소 형태 — codomain 을 Raw 자체로 잡은
Lens.  "213 내부에서 213 을 본다" 의 가장 직접적 구현.

## §3. Injective Lens 존재

`idLens_injective : Function.Injective idLens.view` 직접
귀결.  따라서 note 34 §4 의 정정본에서 언급한 "경계 회피
Lens" (injective) 가 **실제로 존재**.

## §4. Raw 는 Lens-evaluator 로서 서로 구분

`raw_distinguished_by_idLens : Function.Injective (fun r =>
Raw.eval r idLens)`.

즉 Raw → (Lens α → α) 의 idLens-절편이 injective.  Raw
전체가 "Lens 들을 평가하는 함수" 로서 서로 다르다.

## §5. 대각 선택의 의미 재확인

idLens 의 combine 은 대각에서 Raw.a 로 fallback.  이
선택은 view 에 영향 없음 (injective 이므로, note 35
§2 의 diagonal_irrelevant 적용).  Raw.a 대신 Raw.b
또는 다른 임의의 Raw 원소로 바꿔도 동일한 idLens.view = id.

즉 **같은 view 를 주는 Lens 가 무한히 많음** (대각 값의
자유).  이것이 Lens 구조의 redundancy — injective 일 때
대각은 pure ghost.

## §6. 정리

| 질문 | 답 |
|------|-----|
| Q34.1 | 해결 (note 35, DiagonalClassification) |
| Q34.2 | 해결 (note 34 §4 정정, DiagonalIrrelevance) |
| Q34.3 | 부분 해결 (idLens 가 최소 form) |
| Q34.4 | 부분 해결 (self-encoding 대신 Yoneda-dual) |

note 34 의 열린 질문 전부 Lean 으로 기록.

## 변경 이력

- 2026-04-24: Q34.3, Q34.4 의 부분 답.  idLens 구성 +
  Raw.eval Yoneda-dual.  injective Lens 존재 witness.
  `Research/IdentityLens.lean`.
