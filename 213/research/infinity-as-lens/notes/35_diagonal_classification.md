# 35 — Diagonal 거동의 대수적 분류 (Q34.1 해결)

## Note 34 §3 Q34.1 의 답

> diagonal 거동 네 범주 (collapse / idempotent / escalate /
> multiply) 가 대수적으로 meaningful 한 분류인가?

답: **예, 상호 배타적 범주**.  Lean 으로 확인.

## §1. Sq 함수로 재진술

각 Lens 에 대해 **squaring 함수** 정의:

```
sq L : α → α
sq L v := L.combine v v
```

diagonal 거동 = `sq L` 의 모양.

- **Collapse (e)**: `sq v = e` for all v.  상수 함수.
- **Idempotent**: `sq v = v`.  항등 함수.
- **Escalate**: `sq v = v + v` (commutative group 에서).
- **Multiply**: `sq v = v * v` (ring 에서).

## §2. 상호 배타성 (Lean 확인)

`Research/DiagonalClassification.lean`:

`collapse_idempotent_trivial`: L 이 Collapse + Idempotent
를 동시에 만족하면 모든 v = e.  즉 α 는 실질 singleton.

**귀결**: 비자명 α (|α| ≥ 2) 에서 Collapse 와 Idempotent 는
상호 배타.

## §3. 구체 Lens 분류 (Lean 확인)

| Lens | sq | 범주 |
|------|-----|------|
| parityLens | `xor v v = false` | Collapse (e = false) |
| boolAndLens | `v && v = v` | Idempotent |
| boolOrLens | `v \|\| v = v` | Idempotent |
| Lens.leaves | `v + v` | Escalate |
| f9Lens | `v * v` | Multiply |

Lean 정리:

- `parityLens_collapse : Collapse parityLens false`
- `boolAndLens_idempotent : Idempotent boolAndLens`
- `boolOrLens_idempotent : Idempotent boolOrLens`
- `leaves_escalate (v : Nat) : sq Lens.leaves v = v + v`
- `leaves_not_idempotent : ¬ Idempotent Lens.leaves`
- `f9Lens_multiply (v : F9) : sq f9Lens v = F9.mul v v`
- `f9Lens_not_idempotent : ¬ Idempotent f9Lens`
- `f9Lens_not_collapse : ¬ ∃ e, Collapse f9Lens e`

## §4. 대수적 해석

네 범주가 다른 대수 구조에 대응:

- **Collapse**: 2-torsion / involutive structure.
  `v ⊕ v = 0` ≡ 모든 원소가 self-inverse.  𝔽₂-vector
  spaces, Boolean groups.  parityLens 의 xor 가 전형.
- **Idempotent**: semilattice.  `v ∧ v = v`, `v ∨ v = v`.
  order 구조 유도.  min/max, lattice meet/join.
- **Escalate**: torsion-free commutative group.  `v + v = 2v`
  에서 scalar multiplication 출발점.  ℤ, ℝ 류.
- **Multiply**: ring / algebra.  `v²` 가 `v` 에 의해
  결정되지만 linear 하지 않음.  𝔽₉ 같은 field.

즉 네 범주 = 대수 구조의 **근본 갈림길**.  Lens 는 이
갈림길 중 **정확히 하나** 를 선택.

## §5. 다른 범주

- **Involution**: `sq (sq v) = v` 이지만 `sq v ≠ v`.  
  즉 sq 가 non-trivial 대합 (non-constant, non-identity).
  구체 witness: `negSqLens : Lens Bool` with
  `combine u v := if u = v then !u else true` 에서
  `sq v = !v`.  Lean: `Research/NegSqLens.lean`.
  이는 4분류 어디에도 속하지 않음 — Collapse 도 Idempotent
  도 아님이 기계 검증됨.
- **Nilpotent**: `v² = 0` 이지만 `v ≠ 0`.  dual numbers 의 ε
  (F2CDTower 의 `ε * ε = 0`).  Multiply 의 degenerate
  sub-case (codomain 에 nil 원소 존재).
- **Partial**: sq 가 일부 v 에서 미정의 (note 34 §4 정정본).

본질은 네 가지 + special case들.  **완전 분류는 codomain α
의 구조에 의존** — α 의 가능한 α → α 함수 공간 크기가
결정적.  α = Bool 은 4 가능 sq (const T, const F, id, not)
가 각각 Collapse T, Collapse F, Idempotent, Involution 에
대응.

## §6. 다음

Q34.3 (Lens on Lens — Meta-213 구조), Q34.4 (Lens.fromRaw).
Q34.4 의 단순 form 이 다음 후보.

## 변경 이력

- 2026-04-24: Q34.1 답.  sq 함수 + 네 범주 상호 배타성 +
  구체 Lens 분류 Lean 기계 검증.
  `Research/DiagonalClassification.lean`.
