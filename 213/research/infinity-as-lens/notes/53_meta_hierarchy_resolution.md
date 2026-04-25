# 53 — Meta-213 hierarchy 해소: Lens-on-Lens 의 자연 부재 의미

## 질문

"Lens α 의 type 을 codomain 으로 하는 Lens 의 natural 구성":
즉 `Lens (Lens α)` 가 자연스럽게 정의 가능한가?

## 답: 자연 combine 부재가 곧 hierarchy 의 종결 신호

`Lens (Lens α)` 의 정의에 필요한 것:
- `base_a : Lens α`, `base_b : Lens α`
- `combine : Lens α → Lens α → Lens α`

`base_*` 는 임의 Lens α 로 채울 수 있음.  하지만 `combine`
은 `Lens α` 자체 위의 binary op 가 자연스럽지 않음.

### 시도 1: Pointwise sum (α = Nat)

`(L + M).view r := L.view r + M.view r`.  Fold-structured 인가?

- `view (slash x y) = L.view (slash x y) + M.view (slash x y)
                    = L.combine (L.view x) (L.view y) + M.combine (M.view x) (M.view y)`
- 이를 `combine_{L+M}((L+M).view x, (L+M).view y)` 로 표현하려면
  `(L.view x, M.view x)` 를 `(L+M).view x = L.view x + M.view x`
  에서 복원해야 함 — **불가능 (정보 손실)**.

따라서 pointwise sum 은 일반적으로 fold-structured 가 아님.

### 시도 2: 대각 product

prodLens (`Lens (α × β)`) 는 잘 정의되지만 codomain 이 다른 type.
"같은 codomain" 으로 닫힌 binary op 가 없음.

## Meta-213 의 실제 형태: idLens + Yoneda-dual

Note 36 의 결론:
- `idLens : Lens Raw` — self-representation.
- `Raw.eval r α L := L.view r` — Yoneda-dual (Raw 는 Lens-evaluator).

이 둘로 "Meta" 가 완결.  더 위 hierarchy (Lens of Lens of ...)
는 자연 구조 부재로 **존재하지 않음**.

이는 213 의 self-containment 와 정합:
- 모든 추가 layer 는 Lens 의 추가 specification.
- 추가 specification 자체가 Lens 인스턴스.
- 무한 위 hierarchy 가 아니라 **수평 확장** (다른 codomain).

## 형식적 결론

**"Meta-213 hierarchy" 는 open problem 이 아니라 해소된 질문**:
- Lens (Lens α) 의 자연 combine 부재 = hierarchy 의 비-자연
  성 증명.
- idLens + Yoneda-dual 로 모든 self-reference 표현 가능.
- 추가 layer 는 Lens 인스턴스 추가 specification 로 환원.

## 변경 이력

- 2026-04-24: Meta-213 hierarchy 가 open 이 아니라 자연 부재
  로 해소됨을 명시.  idLens + Yoneda-dual 이 충분.
