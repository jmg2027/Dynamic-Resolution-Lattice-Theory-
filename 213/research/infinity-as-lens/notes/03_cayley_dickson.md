# 03 — Cayley–Dickson connection

Mingu flagged this as "looking interesting".  Recording why.

## CD tower, brief

Standard construction:

```
  ℝ  →  ℂ  →  ℍ  →  𝕆  →  𝕊  →  …
 R4    R4    R4    R4    R4 (still)
 R2    R2    ¬R2   ¬R2   ¬R2
 R3    R3    R3    R3    ¬R3
 assoc assoc assoc ¬assoc ¬assoc
```

Each step doubles dimension, applies the "doubling product"

```
  (a, b) · (c, d) = (ac − d·conj b,  conj a · d + c·b)
  conj (a, b)     = (conj a, −b)
```

which preserves **some** axioms and drops others step by
step.

## Correspondence with our Lens catalogue

CD tower is exactly an iterated family of **R4Codomain
candidates** where, level by level, additional Rk's fail.

| Level | Name | R2 | R3 | assoc | R4 | Our analog |
|-------|------|----|----|-------|----|----|
| 0 | ℝ / ℤ | ✓ | ✓ | ✓ | trivial (conj=id), so formally R4-fail | signedLens base |
| 1 | ℂ / ZI | ✓ | ✓ | ✓ | ✓ | ZI (Research) |
| 2 | ℍ / Hurwitz | ✗ | ✓ | ✓ | ✓ | *not yet in catalogue* |
| 3 | 𝕆 / Cayley | ✗ | ✓ | ✗ | ✓ | *not yet in catalogue* |
| 4 | 𝕊 / sedenion | ✗ | ✗ | ✗ | ✓ | similar role to zSqrtProdLens |

So the CD tower is a **natural continuation** of the
R1–R5 independence programme, where each level sharpens
the claim "each Rk is strict" into a hierarchy of
increasingly-weaker codomains, each still R4-admissible.

## Contrast with `zSqrtProdLens` (M4 Direction B)

- `zSqrtProdLens = ZSqrt D₁ × ZSqrt D₂` uses the
  **componentwise** product: loses R3 via `(I,0)(0,I) = 0`.
- CD uses the **twisted** product (quadratic norm-preserving
  doubling): preserves R3 through ℍ and 𝕆; breaks only at 𝕊.
- CD is therefore the "clever" way to double: it reaches
  rank 8 (octonions) while keeping R3.  The componentwise
  product loses R3 immediately at rank 2 = 2.

Structurally: CD's twist `ac − d·conj b` is what makes the
norm stay multiplicative (up to 𝕆).  Componentwise
product's norm `|a|²·|c|² + |b|²·|d|²` is not
multiplicative on `|(a,b)·(c,d)|²`.

## Lean opportunity

Define `CDDouble : R4Codomain A → R4Codomain (A × A)` as
a typeclass-level doubling construction.  (In standard
category theory this is functorial; we avoid the word
"functor" in Raw-adjacent contexts to preserve the
Lens ≠ Functor distinction — see `notes/19_lens_not_functor.md`.)
Instantiate on ZI to get
Hurwitz integers (ℍ-flavored ℤ-lattice) as R4Codomain.
Iterate once more for integer octonions.

Deliverables (future session):
- `Research/CDDouble.lean` — generic doubling construction.
- `Research/ZIx2.lean` — Hurwitz witness.
- `Research/ZIx4.lean` — Cayley-integers witness.
- Note whether R3 actually holds in Lean for these
  (classical fact says yes through 𝕆, fails at 𝕊).

## Connection to the infinity-as-lens thesis

- CD tower is an **infinite** sequence of R4Codomain
  instances (one per natural number).  Each level's
  codomain is countable (as ℤ-lattice); the tower taken
  as a whole is still countable (countable union of
  countables).
- This is consistent with the thesis: the tower is
  finitely-generated (CD doubling rule is finite), but
  produces an unbounded family of codomains.  *No*
  single codomain in the ℤ-tower is uncountable.
- The real-valued tower (ℝ, ℂ, ℍ, 𝕆) imports ℝ's
  uncountability; that's where the infinity ingredient
  enters, and it's a Lens-side phenomenon (choice of
  real-valued codomain vs integer-valued).

## Why it's interesting for us

CD gives a **concrete parametric family** of R4
codomains that, combined with the rest of the
catalogue, pins down *how much* structure each Rk
enforces.  It's also an external cross-check: a
classical algebraic construction falls out as a
special case of the Lens framework.
