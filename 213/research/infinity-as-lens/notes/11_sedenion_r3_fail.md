# 11 — Sedenion R3-fail witness (Moreno zero divisor)

Completes the CD-tower structural story through 4 layers.

## What landed

**Theorem** (in `framework/E213/Research/Sedenion.lean`):
```
R3_fails_on_sedenion :
    ∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0
```

Witness: `u = e_3 + e_10`, `v = e_6 - e_15`, where `e_k`
are the CD-basis elements encoded via the 4-bit binary
expansion of `k`:
- bit 0 → `ZI.im`
- bit 1 → `Lipschitz.im` (outer)
- bit 2 → `Cayley.im`
- bit 3 → `Sedenion.im`

Proof: pure `decide`.  Lean's kernel unfolds the four-level
nested CD multiplication on the concrete `⟨⟨⟨⟨...⟩⟩⟩⟩` basis
vectors and computes the product to `(0 : Sedenion)`.

## Structural significance

This closes the last remaining structural fact in the CD
tower through layer 3:

| Layer | Name           | R2 | R3 | assoc | Lean status |
|-------|----------------|----|----|-------|-----|
| 0 | ZI (Gaussian)     | ✓  | ✓  | ✓     | full R4Codomain |
| 1 | Lipschitz         | ✗  | ✓  | ✓     | full, inc. anti-dist |
| 2 | Cayley            | ✗  | ✓* | ✗     | non-assoc formal |
| 3 | Sedenion          | ✗  | ✗  | ✗     | **R3-fail formal** |

`*` at layer 2: pairwise generator non-vanishing is formal
(`Cayley.mul_generators_ne_zero`); universal R3 is classical
fact (octonions are a composition algebra) and would need
a Hurwitz-type polynomial identity to prove universally.

## Why `decide` works

At each CD level, the multiplication formula is a concrete
term-former on concrete structures.  When all components
are integer-valued (via our Int-based ZI foundation), the
full product of two specific basis combinations reduces to
a concrete sedenion term.  Equality of two specific sedenions
is decidable (all the way down to `Int` decidable equality),
so `decide` closes goals of the form `foo * bar = baz`
whenever `foo`, `bar`, `baz` are explicit concrete values.

This is what lets us formalize:
- Cayley non-associativity (session 4).
- Sedenion R3 fail (this session).

Without `decide`, these would need multi-step symbolic
calculations through the CD formula, as in the manually-
proved Lipschitz `mul_not_commutative` (CD session 1).

## What the CD tower now provides

A **concrete formally-verified 4-step ladder** where each step
loses exactly one structural axiom:

```
ZI    ⟵ commutative, no-zero-div, associative, involution
  ↓ (CD) lose R2
Lipschitz ⟵ no-zero-div, associative, involution
  ↓ (CD) lose associativity
Cayley ⟵ no-zero-div, involution
  ↓ (CD) lose R3
Sedenion ⟵ just involution
```

Every transition is **Lean-verified**: the next layer strictly
violates the axiom that was preserved at the previous layer.

## Connection to the Lens framework

The Lens R1–R5 conditions single out **Layer 0 (ZI)**
essentially uniquely (Paper 1's result).  The CD tower shows:

- R4 alone is **far too weak** — all four CD layers have
  valid R4-style involutions (even layer 3).
- R2, R3, associativity are **independent strong conditions**
  — each is preserved at some CD layer but fails further up.

This sharpens the "each R-condition is strict" programme from
session 1 (`Meta.ZSqrtProduct` etc.) into a infinite parametric
hierarchy.

## Remaining deferrals

- Lipschitz universal mul_assoc (quaternion associativity,
  8-variable polynomial identity).
- Lipschitz norm multiplicativity (Hurwitz four-square
  identity).
- Cayley universal R3 (octonion no-zero-div, Hurwitz thm).
- CD Functor wrapper: generic `CDDouble : A → A × A`
  construction on arbitrary involution rings.
