# 60 — Refines preorder 의 complete lattice 구조 (concrete)

## 결과

`Research/JoinLens.lean` + `Research/LensMeet.lean`:

**Refines preorder = complete lattice (meet + join concrete)**.

- **Meet (greatest lower bound)**: `prodLens L M : Lens (α × β)`
  with view = (L.view, M.view).  Universal property:
  `prodLens_is_meet`.
- **Join (least upper bound)**: `joinLens L M : Lens (Raw → Prop)`
  := `universalLens (JoinEquiv L M)`.  Universal property:
  `joinLens_is_least`.

## 정리 list

- `prodLens_refines_fst`, `prodLens_refines_snd`: meet 이
  lower bound.
- `prodLens_is_meet`: meet 이 greatest lower bound.
- `L_refines_joinLens`, `M_refines_joinLens`: join 이 upper bound.
- `joinLens_is_least`: join 이 least upper bound.
- `joinLens_kernel`: kernel = JoinEquiv (직접 표현).

## 의의

이전에는 universal property 가 abstract level (JoinEquiv 구조)
에서만 확립.  이제 universalLens 구성 으로 **구체 Lens 인스턴스**
로 지정 가능.

따라서 refines preorder 가:
- ⊥: idLens (가장 finer kernel — distinct Raws 모두 distinguish).
- ⊤: constLens (가장 coarse kernel — all Raws same).
- meet: prodLens.
- join: joinLens.

모두 concrete Lens 으로.  **complete lattice**.

## 213 vocabulary 안

이 lattice 구조 가 외부 import 가 아니라 **Lens specifications
의 직접 귀결**.  각 element (meet, join) 가 specific Lens.  추가
axiom 부재.

각 demonstration:
- meet: 두 Lens 의 view 를 pair 로.
- join: JoinEquiv 의 universalLens.
- ⊥, ⊤: idLens, constLens.

## 변경 이력

- 2026-04-25: lattice 구조 의 concrete instantiation 완성.
  Meet (prodLens) + Join (joinLens) 모두 explicit Lens.
