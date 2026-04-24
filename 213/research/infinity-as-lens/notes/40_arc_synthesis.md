# 40 — Note 32-39 arc synthesis: Lens 세계의 구조

## 이 arc 전체의 목적

Note 31-33 의 **자기지시 5 유형** 을 Lens 언어로 번역한 후
(Note 34 §5), Lens 구조 자체를 깊게 탐구.  결과: Lens 세계에
자연스럽고 풍부한 대수적/순서적 구조가 있음을 Lean 으로 확인.

## 전체 그림

```
[AXIOM.md]  — Raw 공리 (3 clause, 1+3 줄)
    |
    v
[Raw]  — 공리적 객체
    |
    v  Lens L : Lens α 에 대해 L.view = unique homomorphism
[Lens.initiality]  (Note 32) — Raw 는 initial Lens-algebra
    |
    v
[Lens 세계]  — α 와 Lens α 들의 집합
    |
    v  refines preorder, diagonal 분류
[Lens 세계의 구조]  (Note 34-39) — 이 arc 의 결과
```

## §1. Lens 세계의 구조 요약

### (a) 각 Lens 의 **diagonal 거동** (local)

`sq L : α → α, sq L v := L.combine v v`.  4 범주 상호 배타
(Note 35):

| 범주 | sq | 대응 대수 |
|------|-----|-----------|
| Collapse | 상수 | 2-torsion / 𝔽₂ |
| Idempotent | 항등 | semilattice |
| Escalate | v+v | torsion-free group |
| Multiply | v² | ring |

Raw 공리는 diagonal 을 **미정의** 로 둠 → Lens 가 채우는
선택이 경계.

### (b) Lens 사이의 **refines preorder** (global)

- ⊥ = **idLens** (Lens Raw, view = id).  finest kernel.
- ⊤ = **constLens e**.  coarsest kernel.
- **meet** = prodLens (product).  Lens L, M 의 kernel 의 교집합.
- **join** 은 자명하지 않음 → Q37.3 open (quotient Lens 필요).

### (c) Refinement 증명 도구

- **`refines_of_factor`**: M.view = g ∘ L.view → L.refines M.
- **`refines_of_morphism`**: structure-preserving h → refinement.

### (d) 구체 catalogue (모두 Lean witness)

```
idLens ⊥
  ⊑
(Lens.leaves, Lens.depth — incomparable)
  ⊑
parityLens, boolXorLens, leafLens — 서로 여러 방향으로 incomparable
  ⊑
(boolAndLens, boolOrLens, constLens) — constant-view 그룹
  ⊑
constLens ⊤
```

**Strict refinements**:
- `Lens.leaves ⊏ parityLens` (parity = leaves mod 2).
- `Lens.leaves ⊏ leafLens` (leaves → leaf/slash 판정).

**Incomparabilities**:
- `Lens.leaves ∥ Lens.depth`.
- `parityLens ∥ boolXorLens` (total vs a-count parity).
- `parityLens ∥ leafLens`.
- `prodLens leaves depth ⊏ idLens` (strict — 같은 (leaves, depth) 다른 Raw 존재).

## §2. 자기지시 5 유형과의 관계 (Note 33 재확인)

| 유형 | Lens 언어 | Lean 위치 |
|------|-----------|-----------|
| 1. value | combine diagonal | Note 34-35 + Research/Diagonal* |
| 2. constructor | Lens.view homomorphism | Note 32 + RawInitiality.lean |
| 3. hierarchy | Lens on Lens (idLens 가 최소 form) | Note 36 + IdentityLens.lean |
| 4. equation | Raw.fold = X = f(X) 고정점 | Lens.view 자체 |
| 5. observer | Raw 의 Yoneda-dual | Raw.eval (Note 36) |

모두 Lens 프레임워크 내에서 자연스럽게 표현.

## §3. Raw 공리와의 연결

Lens 세계의 풍부한 구조는 **Raw 공리 자체에 내재** — 별도
공리 추가 없이 derive.  구체적으로:

1. **Lens.initiality** (Note 32) 가 모든 Lens 의 존재와
   유일성을 보장 — 이는 Raw 가 "initial algebra" 로서의
   universal property.
2. **Diagonal 의 자유** = Raw 의 anti-reflexivity (`x / x`
   미정의) 의 Lens 쪽 대응.  각 Lens 는 이 자유를 자기
   방식으로 채움.
3. **refines preorder** 의 구조는 Lens.view 의 kernel 이
   Raw 의 slash 에 대한 congruence 라는 사실에서 나옴.
4. **meet = product** 은 Raw 의 각 원소가 독립적으로 여러
   Lens 를 evaluate 한다는 단순 관찰.

모든 결과는 공리 추가 없이 derivable.  0 sorry, 0 axiom 유지.

## §4. 남은 열린 질문

- **Q37.3**: quotient Lens = join (Quot 필요).
- **Meta-213 hierarchy**: Lens on Lens 의 더 깊은 구조 (자기
  encoding 의 finite form).
- **Type 5 observer** 의 물리적 실현: 별도 디렉토리 (CLAUDE.md
  지시).
- **Injective Lens 의 classification**: idLens 외 injective
  Lens 의 alternative 구성.
- **refines preorder 의 cardinality**: equivalence class 의
  수 = Raw 의 congruence 수.  countable? uncountable?

## §5. Arc 의 정신

Note 34 이전의 여러 시도들 (Paper 1 의 R1-R5 → ℂ 도출,
r5-critique 등) 은 **특정 구조를 Raw 에서 도출** 하려 함.
이 arc 는 반대 방향 — **Raw 가 어떤 Lens 들을 **허용** 하는가**
를 탐구.  둘은 같은 질문의 다른 방향.

결론: Raw 는 **임의의 Lens-algebra** 를 허용 (Note 32 universal
property).  그 위의 Lens 세계는 자체적으로 풍부한 대수 구조
를 가짐.  Raw 자체는 **무엇** 이 아니라 **경계 없는 잠재** —
각 Lens 가 그리는 경계들의 합집합이 수학의 그림.

## 변경 이력

- 2026-04-24: Note 34-39 arc 를 묶는 synthesis.  Lens
  세계의 구조 완성적 서술 + 자기지시 5 유형과의 대응 +
  Raw 공리와의 연결 + 열린 질문 정리.
