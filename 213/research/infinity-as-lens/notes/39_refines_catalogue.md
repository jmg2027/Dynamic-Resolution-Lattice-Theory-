# 39 — Refines preorder 의 카탈로그 + factoring lemma

## 이 노트의 역할

note 37-38: refines preorder 의 구조 (top / bottom / meet).
이 노트: 구체 Lens 들 사이의 refines 관계 + 통일 증명 도구.

## §1. Factoring lemma (general tool)

`Research/LensFactoring.lean`:

```
theorem refines_of_factor (L M : Lens ...) (g : α → β)
    (hfactor : ∀ r, M.view r = g (L.view r)) :
    L.refines M
```

**읽기**: "M.view 가 L.view 를 통해 factor 되면 L 이 M 을
refine."  M 은 L 의 정보만 사용.

역방향 (refines → factor) 은 비건설적 (AC 필요) — 이
파일은 건설적 방향만 제공.

## §2. Catalogue (지금까지 Lean 확인)

```
                idLens (⊥)
               /        \
         Lens.leaves ∥ Lens.depth    (incomparable)
               :        :
         parityLens (leaves_refines_parity)
               :
         boolAndLens, boolOrLens (const true)
               :
         constLens e (⊤)
```

### Strict refinements (⊏)

- `Lens.leaves ⊏ parityLens` — `LeavesRefinesParity.lean`.
  parity = leaves 의 홀짝.  strict by witness
  (Raw.a vs sample3 = 같은 parity 다른 leaves).

### Incomparability (∥)

- `Lens.leaves ∥ Lens.depth` — `LeavesDepthIncomparable.lean`.
  - `leaves_not_refines_depth`: witness rDeep/rBalanced
    (같은 leaves=5, 다른 depth).
  - `depth_not_refines_leaves`: witness
    rShallowNarrow/rShallowWide (같은 depth=3, 다른 leaves).

### Trivial refinements

- `idLens` 는 모든 Lens 를 refine (`idLens_refines_all`).
- 모든 Lens 가 `constLens e` 를 refine (`all_refine_constLens`).

## §3. 관찰

1. **Raw 공리로부터 분리된 Lens 사이의 independent 구조 존재**.
   leaves 와 depth 는 둘 다 Raw 로부터 정보를 뽑지만, 서로
   직교.
2. **Factoring lemma 가 모든 refines 증명의 공통 루트**.
   concrete Lens 관계는 factor function g 를 찾는 문제로
   귀착.
3. **Incomparability 는 진정한 poset 구조의 증거** — refines
   는 total order 가 아님.

## §4. 새 열린 질문

- **Q39.1**: refines preorder 의 chain decomposition?
  maximum chain 의 구조?
- **Q39.2**: `prodLens leaves depth ⊏ idLens` 엄격.  witness?
- **Q39.3**: 모든 refines 경로가 factor function 으로 realize?

## 변경 이력

- 2026-04-24: refines catalogue + factoring lemma.  구체
  Lens 관계 두 건.  `LensFactoring.lean`,
  `LeavesDepthIncomparable.lean`.
