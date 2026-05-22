# G69: Addition as slash-projection — fold-of-fold structure

## User insight (2026-05-09)

> "우리가 아는 자연수 더하기를 생각해보면 일단 항등렌즈에 atomcount
> 렌즈를 씌운 가장 단순한 형태를 생각해보면, 여러게 세는거겠지?
> 근데 렌즈들은 다 카타모피즘이니까(fold니까) atomcount를 fold하는
> 연산인가 그럼?  Fold의 횟수?  Fold를 fold fold…하는?"

## Core claim

**Natural-number addition is NOT a primitive operation.**

It's the **image of Raw's `slash` under the atomCount lens**.

```
Raw                            Nat213
  slash : Raw × Raw → Raw  ──atomCount─→  add : Nat213 × Nat213 → Nat213
```

Under `lensLeafCount = (1, 1, +)`:
- `Raw.slash x y` projects to `(atomCount x) + (atomCount y)`
- The `+` here IS `Nat213.add`

So **`+` is the codomain image of `slash`**.  Not foundational; derived.

## Formal theorem (∅-axiom)

```lean
theorem slash_projects_to_add (x y : Raw) (h : x ≠ y) :
    lensLeafCount.apply (Raw.slash x y h)
    = Nat213.add (lensLeafCount.apply x) (lensLeafCount.apply y)
```

This is proved as `lens_slash_decomposition lensLeafCount Nat213.add_comm`
— direct application of the catamorphism property.

Concrete witness: `atomCount_slash_ab : lensLeafCount.apply rawAB = Nat213.two`
(= 1 + 1 = 2).

## Fold-of-fold structure

User's intuition "Fold를 fold fold…?": YES, addition itself involves
nested folds.

### Layer 1: Raw → Nat213 (catamorphism)

`lensLeafCount.apply : Raw → Nat213` is a **fold over Raw's
recursive structure** (the `slash` recursion).  Each Raw is
catamorphism-mapped to a Nat213 element.

### Layer 2: Nat213.add (= succ-fold)

`Nat213.add` is itself a **fold over Nat213's recursive structure**
(the `succ` recursion):

```lean
def add : Nat213 → Nat213 → Nat213
  | one,    n => succ n
  | succ m, n => succ (add m n)
```

This recurses on the FIRST argument: `add m n` = "iterate `succ` m
times starting from n".  This IS a catamorphism on Nat213's
`one | succ` structure (fold the unary peano number).

### Composition: the slash-projection theorem

When we add two atomCount-fold results:
```
(apply r1) + (apply r2)
=  (Raw-fold of r1)  +  (Raw-fold of r2)
=                   ↓
       Nat213-fold (= add) of the two Raw-folds
```

So the projection `slash → add` involves **two fold layers**:
- Outer fold: Raw → Nat213 (1 step per slash recursion)
- Inner fold: Nat213.add (succ-iteration on the first arg)

= **fold-of-fold** structure.

## Why this matters

### 1. Addition isn't foundational

In standard math, `1 + 1 = 2` is taken as primitive.  In 213-native:
- Raw is foundational (atom + slash recursion)
- Nat213 emerges as a lens-codomain
- Addition emerges as the IMAGE of slash via the canonical
  counting lens

So `1 + 1 = 2` becomes:
- Raw `a` has atomCount 1
- Raw `b` has atomCount 1
- Raw `slash a b` has atomCount 1 + 1 = 2 (by `atomCount_slash_ab`)

The "+" emerges; it's not primitive.

### 2. Different lenses → different "addition-likes"

For combine = `+`: slash projects to `Nat213.add`
For combine = `·`: slash projects to `Nat213.mul`
For combine = `max`: slash projects to `max`

Each lens produces a different "binary operation on Nat213"
derived from slash.  Standard addition is just one canonical
choice.

### 3. The lens family corresponds to the algebra family

| Lens (ba, bb, combine) | Nat213-algebra image |
|---|---|
| (1, 1, +) | (Nat213, +) — additive monoid |
| (1, 1, ·) | (Nat213, ·) — multiplicative monoid |
| (1, 1, max) | (Nat213, max) — max-semilattice |
| (n, m, c) | (Nat213, c) — generic algebra |

So the **lens family at codomain Nat213 ≅ family of algebras on Nat213**.

This is the categorical reading: a lens IS an algebra-structure
homomorphism from Raw (free algebra on atoms) to (Nat213, ba, bb, c).

## Lean ∅-axiom inventory (this session)

`Theory/Nat213/Core.lean`: 10 ∅-axiom theorems
  (Nat213 type, closure, no-absorption, add_one_right,
   add_succ_right, add_comm, mul_one, one_mul, mul_two_grows,
   no_absorbing_element, toNat_ge_one, add_succ_left, one_add)

`Theory/Nat213/Lenses.lean`: 19 ∅-axiom theorems
  (Lens definitions, catamorphism properties, lens infinity,
   fractal properties, atom = Nat213.one, slash_projects_to_add,
   fold_of_fold_witness, etc.)

**Total: 29 ∅-axiom theorems** in Nat213-framework.

## See also

- `lean/E213/Theory/Nat213/Core.lean` — Nat213 type + arithmetic
- `lean/E213/Theory/Nat213/Lenses.lean` — lens framework
- `research-notes/G65–G68` — prior synthesis chain
