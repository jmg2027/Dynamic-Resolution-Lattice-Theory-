# F1 — Generic cutBinary kernel ('213 스럽게 generic')

## User directive (2026-04-26)

> "Generic 으로 213 스럽게 가보자."

기존 cutSum, cutMul 의 specific 구현 → universal abstraction 으 로
elevate.

## Generic framework

### `cutBinary` 의 universal kernel

```
cutBinary P k1 k2 M1 M2 cx cy
  := ∃ m1 ≤ M1, m2 ≤ M2, P m1 m2 ∧ cx(m1, k1) ∧ cy(m2, k2)
```

2D bounded search over (m1, m2) — predicate-driven.

### `CutBinaryOp` struct

```
structure CutBinaryOp where
  predicate : Nat → Nat → Nat → Nat → Bool
  k1 k2 M1 M2 : Nat → Nat → Nat
```

모든 binary cut operation 의 *parameter space*.

### Instance pattern

```
def cutSumOp : CutBinaryOp where
  predicate := fun m _ m1 m2 => decide (m1 + m2 = 2*m)
  k1 := fun _ k => 2*k
  k2 := fun _ k => 2*k
  M1 := fun m _ => 2*m
  M2 := fun m _ => 2*m
```

### Generic theorem

`CutBinaryOp.apply_locallyDetermined` : op.apply 가 locally determined.

**모두 0 axioms!**

## Special cases

### Trivial (search-free) operations

cutMax, cutMin = pure Bool combinators (cx ∧ cy or cx ∨ cy).
- 검 색 부 재.
- Continuity 자명.
- Commutativity, associativity 모두 funext + cases 로 (axiom: Quot.sound).

cutMax 가 cut framework 의 가 장 elegant 한 operation.

### Search-based operations

cutSum, cutMul = cutBinary 의 specific instance.
- Bounded 2D search.
- Bishop ε-precision 의 implementation detail (k1, k2 factor).
- Continuity 자동 유 도.

## 213-style 의 의의

1. **Lens-style abstraction**: 모든 binary cut operation 이 single
   structural form.
2. **Substrate uniformity**: 미 래 모든 operation 이 같은 kernel 의
   instance.
3. **Auto-derived properties**: locally-determined 가 generic theorem.
4. **Axiom-free generic**: cutBinary_locallyDetermined 가 0 axioms.

## Future generic directions

- **Symmetric predicate → commutativity**: P(a, b) = P(b, a) → op
  commutes.  Bijection-based proof.
- **Monotonic predicate → monotonicity**: P → P' implies app result
  monotone.
- **Composition**: f ∘ g 의 LDD (`composeLDD`) — already done.
- **CutAlgebra typeclass**: 0, 1, +, ×, max, min 등 통합.

## Cross-references

- `framework/E213/Research/Real213CutBinary.lean` — generic kernel.
- `framework/E213/Research/Real213CutBinaryOp.lean` — struct +
  instances + apply.
- `framework/E213/Research/Real213CutBinaryInstances.lean` — direct
  cutSum/cutMul via cutBinary.
- `framework/E213/Research/Real213CutMaxMin.lean` — trivial ops.
- `notes/F0_213_native_arithmetic_synthesis.md` — earlier synthesis.
