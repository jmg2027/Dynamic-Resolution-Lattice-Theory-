# 05 — Σ2 formalised: Raw ≈ ℕ

Follow-up to session 1 (notes/04).  Σ2 (Raw → ℕ
injective) now has a Lean proof in the core library
(Mathlib-free).

## New modules

- `framework/E213/Infinity/Pair.lean`
  `pair x y := 2^(x+y) + y`, injective on `ℕ × ℕ`.

- `framework/E213/Infinity/Godel.lean`
  `Tree.toNat` Gödel numbering and its injectivity;
  lifted to `Raw.toNat`; packaged `raw_at_most_countable`
  and `raw_equipotent_nat`.

## Mathematical content

### Pairing function

The pairing `pair x y = 2^(x+y) + y` is chosen over the
classical Cantor pairing `(x+y)(x+y+1)/2 + y` because
its injectivity proof is entirely omega-friendly once
one has `Nat.lt_two_pow_self` (in Lean 4 core) — no
division or square root is needed.

Argument:
- `pair x y < 2^(x+y+1)` (upper bound)
- `2^(x+y) ≤ pair x y` (lower bound)
- For `x₁+y₁ ≠ x₂+y₂`, the two pairings live in
  disjoint intervals `[2^k, 2^(k+1))`, so they cannot
  be equal.
- For `x₁+y₁ = x₂+y₂`, the tail `+y` distinguishes.

### Tree Gödel numbering

```
  a       → 0
  b       → 1
  slash x y → 2 + 2·pair(toNat x, toNat y)
```

Parity and range separate the three constructors
(`slash` is always `≥ 2` and even).  Within the `slash`
branch, `pair`'s injectivity reduces to equal child
Gödel numbers, hence by IH equal children, hence equal
Trees.

### Raw lift

`Raw.toNat r := r.val.toNat`.  Injectivity is immediate
by `Tree.toNat_injective` and `Subtype.ext`.

## Σ2 ∧ Σ3 — Raw is countable

```
theorem raw_equipotent_nat :
    (∃ f : Nat → Raw, Function.Injective f) ∧
    (∃ g : Raw → Nat, Function.Injective g)
```

Both directions are concrete — `rawTower` (Σ3) and
`Raw.toNat` (Σ2).  No Schröder–Bernstein, no classical
choice.  Raw is at-most-countable and at-least-countable
simultaneously, matching the mathematician's "Raw is
countably infinite" reading.

## Consequence for the infinity-as-Lens thesis

With Σ2 + Σ3 + Σ5 + Σ6 all formal:

- Raw's cardinality: **exactly ℕ** (countable).
- Observations via function spaces: Cantor tower —
  `Raw → Bool` uncountable; `(Raw → Bool) → Bool`
  strictly larger; etc.
- All this from an axiom making **no cardinality
  postulate**.  The cardinality stack is read off as
  observation, not written in as input.

Σ7 (the meta-statement) can now be written in prose with
all four supporting theorems cited by Lean name.

## What's left in the roadmap

- Σ4: Lens-image cardinality consolidation table.
- Σ7: meta write-up citing Σ2 / Σ3 / Σ5 / Σ6 formally.
- CD doubling (note 03) — future session.
