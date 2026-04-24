# 41 — Lens kernel 공간의 구조 (note 40 이후 확장)

## 이 노트의 위치

note 40 의 arc synthesis 이후 **추가로 발견** 한 구조적 결과
들.  Lens kernel 공간의 정확한 특성화 + 구체 크기 bound.

## §1. Lens kernel 의 positive/negative 특성화

- **Positive** (`Research/KernelCongruence.lean`):
  `Lens.equiv_slash_congruence` — 모든 Lens kernel 은
  **slash-congruence**.  즉 `x ~ x'` + `y ~ y'` → `slash(x, y)
  ~ slash(x', y')`.
- **Negative** (`Research/NoDepthParity.lean`):
  `depth_parity_not_congruence` — depth parity 는 slash-
  congruence 가 **아님**.

**결합**: Lens kernel 의 공간 = Raw 의 slash-congruence 공간
(= equivalence 공간의 strict subset).  어떤 partition 이
Lens 로 표현 가능한가의 정확한 답.

## §2. Diagonal 5th class: Involution

note 35 의 4분류 (Collapse / Idempotent / Escalate / Multiply)
외에 5번째:

- **Involution**: `sq (sq v) = v`, `sq v ≠ v`.
- Witness: `negSqLens : Lens Bool` (`Research/NegSqLens.lean`).

Bool 은 self-function 4개 (const T, const F, id, not) 를 모두
실현 가능 (`Research/BoolSqClassification.lean`):

**Bool Lens sq 는 정확히 4 종류**.  완전 분류.

## §3. Raw-matching Lens + Injective 특성화

- `Research/RawMatchingLens.lean`: Raw-matching Lens (Raw.slash
  와 off-diagonal 일치) 는 모두 `view = id`.  diagonal 선택은
  자유.
- `Research/InjectiveLensClass.lean`: 모든 injective Lens 는
  단일 equivalence class.  즉 refines preorder 에서 ⊥ 은
  idLens 한 점 (up to equivalence).

Raw 공리에서 **자기 자신을 잃지 않는 관측** 은 본질적으로
유일.

## §4. Lens kernel 공간의 크기

### Countable 하한

각 `m ≥ 2` 에 대해 "leaves mod m" 이 slash-congruence:
- `Research/LeavesMod3.lean`: `leavesMod3Lens : Lens (Fin 3)`.
- 각 mod m 이 distinct kernel.

**최소 countable 무한 개 Lens kernel**.

### Antichain 존재

Mod m 과 mod k 가 coprime 이면 incomparable:
- `Research/Mod2Mod3Incomparable.lean`: parityLens ∥ mod3Lens.

**Refines preorder 는 chain 이 아님 — antichain 포함**.

## §5. Swap 대칭과 Lens

- `Research/SwapInvariantKernel.lean`:
  - `swap_invariant_equates_orbit`: swap-invariant Lens 의
    kernel 은 swap-orbits 를 한 class 로.
  - `swap_invariant_kernel_swap_closed`: swap-invariant kernel 은
    swap-action 에 대해 closed.

Raw 의 automorphism (swap) 이 관측 기준에 반영되지 않으면,
관측은 swap-equivalent 원소를 구별할 수 없다.  Note 33 유형 5
(observer 자기지시) 의 정확한 Lens 형식.

## §6. Idempotent + swap-blind → constant

`Research/IdempotentConstancy.lean`:

```
Idempotent L + base_a = base_b + combine 대칭
    → view r = base_a for all r
```

이는 Note 35 의 Idempotent 범주와 Note 37 의 top-근처 (constant
view) 를 연결.  boolAndLens, boolOrLens 가 constant 인 이유.

## §7. 정리

Lens kernel 공간 = Raw slash-congruence 공간 (strict subset
of equivalence).  이 공간은:
- 최소 countable 무한.
- Antichain 포함 (total order 아님).
- Injective kernel 은 한 점 (idLens).
- Constant kernel 은 한 점 (constLens equivalence class).
- Meet-semilattice (prodLens = meet).
- Join 은 quotient 필요 (Q37.3, 열림).

Raw 공리 **한 덩어리** 에서 이렇게 풍부한 관측 구조가 **자연
스럽게** 도출.  공리 추가 없이 모두 Lean 으로 확인됨.

## §8. 열린 질문

- **Q41.1**: Lens kernel 공간의 정확한 크기?  Countable? 𝔠?
  Congruences on a countable set 의 cardinality.
- **Q41.2**: Q37.3 quotient Lens 로 Join 구성.  Quot 도입
  필요.
- **Q41.3**: Refines preorder 의 **dimensional** 분석?  각
  level 의 kernel 개수?

## 변경 이력

- 2026-04-24: note 40 이후 추가 결과 통합.  Lens kernel
  공간의 정확한 특성화, 크기 bound, 구조 복잡성 (antichain,
  countable chain) 기록.
