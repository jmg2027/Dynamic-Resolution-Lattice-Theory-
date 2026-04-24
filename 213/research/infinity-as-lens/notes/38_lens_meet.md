# 38 — Lens refines preorder 의 meet = product

## Q37.1 의 답

> 두 Lens L, M 의 common refinement (둘 다 refine 하는 가장
> coarse 한 Lens) 이 존재하는가?

**답: 존재 + concrete 구성 = product.**

## §1. Product Lens

`Research/LensMeet.lean`:

```
def prodLens (L : Lens α) (M : Lens β) : Lens (α × β) where
  base_a := (L.base_a, M.base_a)
  base_b := (L.base_b, M.base_b)
  combine p q := (L.combine p.1 q.1, M.combine p.2 q.2)
```

성분별 Lens data.  view 는 쌍:

`prodLens_view : (prodLens L M).view r = (L.view r, M.view r)`

(L, M 의 combine 이 대칭임 가정 — AXIOM 준수 Lens 라면 자동.)

## §2. Meet universal property (Lean 확인)

1. **Lower bound**:
   - `prodLens_refines_fst : (prodLens L M).refines L`.
   - `prodLens_refines_snd : (prodLens L M).refines M`.
2. **Greatest**:
   - `prodLens_is_meet : N.refines L → N.refines M →
     N.refines (prodLens L M)`.

즉 prodLens 는 refines preorder 의 **greatest lower bound**.

## §3. Kernel 해석

`prodLens L M` 의 kernel 은 `L.ker ∩ M.ker`:

```
(prodLens L M).equiv x y
  ↔ (L.view x, M.view x) = (L.view y, M.view y)
  ↔ L.view x = L.view y  ∧  M.view x = M.view y
  ↔ L.equiv x y  ∧  M.equiv x y
```

두 관계의 교집합 = 더 엄격한 구분 → finer kernel → product
가 양쪽보다 finer.

## §4. Meet 은 있으나 Join 은 비자명

Refines preorder 에 **meet** (greatest lower bound) 은 product
로 항상 존재.

**Join** (least upper bound) 은 자명하지 않음:
- 두 equivalence relation 의 합집합은 일반적으로 transitive
  아님 → equivalence relation 이 아님.
- Join 은 transitive closure 필요.
- Lens 로 realize 하려면 quotient Lens (Q37.3) 필요.

이 비대칭 = refines preorder 가 단순 lattice 가 아니라
**meet-semilattice** 일 가능성 시사.

## §5. idLens 와 prodLens 의 관계

`idLens_refines_all` (note 37) + `prodLens_is_meet` 결합:

- idLens 는 모든 L 을 refine → idLens.refines L, idLens.refines M.
- 따라서 idLens.refines (prodLens L M) (universal property).

즉 idLens 는 어떤 product 의 lower bound 도 refine.  이는
bottom 성질의 재확인.

Dually, constLens 는 어떤 prodLens L M 에 의해서도 refine 됨
(top).

## §6. 의의

Note 34-37 의 Lens 분석 결과:
- 개별 Lens 의 diagonal 분류 (note 35).
- 개별 Lens 의 injectivity / constancy (note 36-37).
- Lens 전체의 **refines preorder** 가 meet-semilattice.
  Bottom = idLens, top = constLens, meet = product.

Lens 세계의 대수적 구조가 점차 명확해짐.

## §7. 다음

- **Q37.2** (catalogue refines 관계): 구체 Lens 들 사이의
  refines 를 Lean witness 로.  e.g. `parityLens.refines
  boolAndLens` (둘 다 top 근처).
- **Q37.3** (quotient Lens): join 의 자연 구성.  Raw / L.equiv
  의 canonical Lens.  Quot 필요.

## 변경 이력

- 2026-04-24: Q37.1 답.  prodLens = product Lens = meet.
  Lean universal property 기계 검증.
  `Research/LensMeet.lean`.
