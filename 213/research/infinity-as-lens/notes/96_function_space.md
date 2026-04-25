# 96 — Function space: `α → β` 도 의미 framework instance

`Research/FunctionSpace.lean` — `HasDistinguishing β + Inhabited α
→ HasDistinguishing (α → β)`.

## 결과

```lean
def funHasDistinguishing (α β : Type) [Inhabited α]
    [d_β : HasDistinguishing β] : HasDistinguishing (α → β)

def boolFunUniversal : Raw → (Bool → Bool) :=
  funUniversalMorphism Bool Bool (...)
```

[Quot.sound] only.

## 의의

functional type 도 framework 의 instance — categorical exponential.

추가 instance catalogue:
- Bool, Fin 3, Nat, Int (basic types).
- Pair (categorical product).
- Lens α (Lens-on-Lens).
- α → β (function space).

framework 가 *type constructors* (product, exponential) 위 closed —
ordinary type theory 의 모든 type 이 framework 의 instance 가능.

## Complete semantic 213 proof 의 evidence

- type 의 거의 모든 form (basic, product, function, Lens) 이
  HasDistinguishing instance 가능.
- → 의미 를 갖는 거의 모든 type 이 framework 안 representable.
