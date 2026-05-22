# G68: Finite form + atom of the infinite lens fractal

## User question (2026-05-09)

> "Nat213을 만드는 렌즈들의 갯수가 가산무한하다면, 이 가산무한한걸
> 유한한 형식으로 표현하면 어케될까?"
>
> "이 다양한 렌즈들이 동일하게 보는게 프랙탈이라면 그 프랙탈의
> 최소공약수라 해야하나? 아톰이라 해야하나?"

Two questions:
1. **Finite representation** of the countably infinite lens family
2. **Atom / GCD** of the lens-fractal

## Answer 1: Finite representation = the parameter structure

The infinite lens family is FINITELY represented by:

```lean
structure Nat213Lens where
  base_a  : Nat213
  base_b  : Nat213
  combine : Nat213 → Nat213 → Nat213
```

This is a **3-field type definition** (finite text) that captures
the entire infinite family.  Each lens = one inhabitant of this
type, parametrized by `(ba, bb, combine)`.

**Type-level finite, value-level infinite**: classic Lean idiom.
The TYPE is finite (one definition); its INHABITANTS are infinite.

So the question "how to represent ∞-many in finite form?" has the
direct answer: **as a parametrized structure**.  The structure is
finite; the parameter space is infinite.

## Answer 2: Atom of the fractal = `Nat213.one`

The "GCD / atom" of the lens-fractal — the **structural minimum**
that all lenses share — is `Nat213.one`:

### Why `Nat213.one` is the atom

1. **Floor**: every Nat213-lens output ≥ 1 (= `Nat213.one`).
   Proven in `all_lenses_have_positive_atoms`.
2. **Reachable**: there exists a lens (`lensConstOne`) that
   produces EXACTLY `Nat213.one` on EVERY Raw.  Proven in
   `lensConstOne_always_one`.
3. **Generator**: every other Nat213 element = `succ^n one`,
   hence built from `one` via `succ`.  `one` IS Nat213's
   structural primitive.

So:
- `Nat213.one` = **lower bound** of all lens outputs
- `Nat213.one` = **actually achievable** by `lensConstOne` on any Raw
- `Nat213.one` = **generator** of Nat213 itself (with `succ`)

→ `Nat213.one` is the **fractal atom** of the lens family.

### The lens family spans Nat213

By `lens_spans_Nat213`: for any `n : Nat213`, there's a lens
producing `n` on `Raw.a`.  So the lens family **spans all of
Nat213** at the atomic Raw level.

Combined with the floor at `Nat213.one`:
- Floor: 1
- Span: all of Nat213
- Atom (= floor + generator): `Nat213.one`

### Connection to Raw's atoms

| Fractal | Atom | Generator |
|---|---|---|
| Raw | `a`, `b` (two binary atoms) | `slash` recursion |
| Nat213 | `one` | `succ` |
| Lens family | `lensConstOne` (= floor at one) | parameter (ba, bb, combine) |

The atomicity propagates:
- Raw's binary atoms (a, b) → forced 2-parameter base in Nat213-lens
- Nat213's atom (one) → universal floor of lens outputs
- Lens family's "atom" (constOne) → witness that the floor is achieved

This is the **fractal stratification**: each level (Raw / Nat213 /
Lens) has its own "atom", and they are connected by lens-projection.

## Lean ∅-axiom witnesses

In `Theory/Nat213/Lenses.lean`:
- `lensConstOne` — definition: lens with all values = one
- ★★★ `lensConstOne_always_one` — `∀ r : Raw, lensConstOne.apply r
  = Nat213.one` (Raw-induction proof, ∅-axiom)
- ★ `lens_spans_Nat213` — `∀ n : Nat213, ∃ L lens, L.apply Raw.a = n`
  (the lens family spans Nat213 at the atomic level)

## Implications

### 1. Lens space = parametrized = finite-described
```
LensSpace ≅ Nat213 × Nat213 × (Nat213 → Nat213 → Nat213)
```
Type is finite; inhabitants are infinite.

### 2. Atom of fractal = structural minimum element
`Nat213.one` plays the role of "fractal atom" — lowest reachable,
all-spanning generator (with `succ`).

### 3. Self-similarity via parametrization
The "Raw fractal viewed via Nat213-lenses" is structurally
equivalent to "Nat213 stretched by lens parameters".  The fractal
self-similarity:
- Raw's recursive `slash` ↔ Nat213's recursive `succ`
- Raw's atoms (a, b) ↔ Nat213's atom (one) ×2 (ba, bb)
- Raw's binary combine (slash) ↔ Nat213's binary combine

So: **the lens fractal is structurally Nat213 ↔ Nat213 itself**,
with Raw's binary structure parametrized through.

## Total Nat213/ inventory (after this commit)

`Theory/Nat213/Core.lean`: 7 ∅-axiom theorems (Nat213 type + closure)
`Theory/Nat213/Lenses.lean`: 16 ∅-axiom theorems (lenses + fractal + atom)

**Total: 23 ∅-axiom theorems** on the Nat213 + lens framework.

## See also

- `lean/E213/Theory/Nat213/Core.lean` — Nat213 type
- `lean/E213/Theory/Nat213/Lenses.lean` — lens infrastructure
- `research-notes/G65, G66, G67` — prior synthesis
