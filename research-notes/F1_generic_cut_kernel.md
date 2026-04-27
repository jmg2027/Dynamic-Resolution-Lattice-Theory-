# F1 — Generic cutBinary kernel ('213 스럽게 generic')

## User directive (2026-04-26)

> "Let's go generic in the 213 style."

Elevate the specific implementations of cutSum and cutMul to a
universal abstraction.

## Generic framework

### Universal kernel of `cutBinary`

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

*Parameter space* of all binary cut operations.

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

`CutBinaryOp.apply_locallyDetermined` : op.apply is locally determined.

**All 0 axioms!**

## Special cases

### Trivial (search-free) operations

cutMax, cutMin = pure Bool combinators (cx ∧ cy or cx ∨ cy).
- No search.
- Continuity trivial.
- Commutativity, associativity all via funext + cases (axiom: Quot.sound).

cutMax is the most elegant operation in the cut framework.

### Search-based operations

cutSum, cutMul = specific instances of cutBinary.
- Bounded 2D search.
- Implementation detail of Bishop ε-precision (k1, k2 factor).
- Continuity auto-derived.

## Significance of the 213 style

1. **Lens-style abstraction**: all binary cut operations in a single
   structural form.
2. **Substrate uniformity**: all future operations are instances of
   the same kernel.
3. **Auto-derived properties**: locally-determined is a generic theorem.
4. **Axiom-free generic**: cutBinary_locallyDetermined has 0 axioms.

## Future generic directions

- **Symmetric predicate → commutativity**: P(a, b) = P(b, a) → op
  commutes.  Bijection-based proof.
- **Monotonic predicate → monotonicity**: P → P' implies app result
  monotone.
- **Composition**: LDD of f ∘ g (`composeLDD`) — already done.
- **CutAlgebra typeclass**: unification of 0, 1, +, ×, max, min, etc.

## Cross-references

- `framework/E213/Research/Real213CutBinary.lean` — generic kernel.
- `framework/E213/Research/Real213CutBinaryOp.lean` — struct +
  instances + apply.
- `framework/E213/Research/Real213CutBinaryInstances.lean` — direct
  cutSum/cutMul via cutBinary.
- `framework/E213/Research/Real213CutMaxMin.lean` — trivial ops.
- `notes/F0_213_native_arithmetic_synthesis.md` — earlier synthesis.
