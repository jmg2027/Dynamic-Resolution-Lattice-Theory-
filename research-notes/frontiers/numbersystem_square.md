# The number-system square: two Lenses, two orders, one ℚ

## The square

```
        difference pair (+-question)
   ℕ ────────────────────────────▶ ℤ
   │                               │
   │ ratio pair                    │ ratio pair
   │ (×-question)                  │ (positive denominator)
   ▼                               ▼
   ℚ₊ ───────────────────────────▶ ℚ
        difference pair of ℚ₊
```

Four paths, two composite routes (ℕ→ℤ→ℚ and ℕ→ℚ₊→ℚ); a rational is a
nested ℕ-pair in two bracketings.  The ℕ→ℤ→ℚ route is closed
(`Rat213`: Int numerator × positive Nat denominator, normal form
exact).  The ℕ→ℚ₊ leg is `RatioLensFounding.ratioEquiv`; the ℚ₊→ℚ leg
(difference pairs of positive ratios) is **not yet built**.

## Why the routes converge (the principle, to be made a theorem)

**Distributivity is the commutation law of the two Lenses.**  The
difference fiber is a +-action `(a,b) ~ (a+c, b+c)`; the ratio fiber
is a ×-action `(a,b) ~ (ka, kb)`; `k(a+c) = ka + kc` says the
×-transport maps +-fibers to +-fibers, so quotienting in either order
lands in the same place.  Repo pins: the mixed keystone
`Int213.subNatNat_mul_ofNat` (difference pair × scalar), the ∣-side
`Gcd213.gcd213_mul_left`, and the canonical target
`Rat213.lowest_exists`/`lowest_unique` (any presentation normal-forms
to sign × coprime pair).  Contrast: where commutation *fails* —
order × sign, `OrderMul.mul_le_mul_right_nonpos` — the square does
not close and the positive cone must be carved out first.  Same
phenomenon, positive and negative instances.

## The detectors (judgment formulas across levels)

Each rung's judgment formula becomes, one level up, the membership
detector of the old system and the normal-form selector of the new:

| formula | in ℕ | in ℤ / ℚ₊ | in ℚ |
|---|---|---|---|
| sandwich (order) | witness dichotomy (`witness_total`/`not_both`) | sign readout (`subNatNat_eq_ofNat_iff`/`negSucc_iff`) | floor / integer part (`div_sandwich` lifted); ℤ-membership = denominator 1 |
| coprimality (∣) | a relation between two naturals | lowest-terms selector (`gcd_strip_coprime` + `coprime_repr_unique`) | canonical representative (`IsLowest`); ℕ/ℤ-membership = `b ∣ a`; Farey `det P = 1` |

In ℚ the two detectors are exactly the two normal-form projections:
order frame → sign + integer part; ∣ frame → coprime magnitude pair.

## Open bricks

1. The ℚ₊→ℚ leg: difference pairs over positive ratio pairs, with its
   own sandwich (cross-subtraction) — all over ℕ⁴.
2. **Square-commutes theorem** (PURE): the ℕ→ℚ₊→ℚ composite and the
   ℕ→ℤ→ℚ composite normal-form to the same `Rat213` representative;
   the proof content should be exactly distributivity.
3. The Lens-frame reading (one fact, several frames — morphism / added
   axis / boundary): essay after the Lean closes, not before.

## The equation ladder (extension of the square)

Each system is the totality domain of an equation class with ℕ
coefficients and **one unknown**:

| class | completion |
|---|---|
| `x + b = c` (monic, +) | ℤ |
| `a·x = b` (×) | ℚ₊ |
| `a·x + b = c` (general degree 1) | ℚ |
| monic polynomial | algebraic integers |
| general polynomial | algebraic numbers |

Two rules to pin: (i) class = one reversed arrow + closure under the
available folds; degree = ×-question iterated on the unknown;
(ii) **monic ↔ ring-like, general leading coefficient ↔ field-like**,
persisting up the ladder.  Boundary: non-polynomial questions
(`a^x = b`) leave equation-completion for sandwich-family completion
(ℝ order-frame, ℚ_p ∣-frame).

## Collapse vs rigid axis (the doubling dichotomy)

A pair-Lens either *collapses* (quotient by the operation's action —
ℕ→ℤ→ℚ, dimension stays 1) or stays a *rigid axis* (ℚ(√2) over ℚ;
ℝ→ℂ→ℍ→𝕆 Cayley–Dickson, dimension 1→2→4→8).  Criterion: **per-frame
visibility of the obstruction readout** — sign (2-valued) and
remainder (`a`-valued) are old-data-visible → collapse; `x² = 2` is
order-visible (sandwich locates it → absorbed by ℝ) but
algebra-invisible (rigid 2-dim over ℚ); `x² = −1` is invisible in
every frame (`Int213.int_sq_nonneg` is the positivity certificate)
→ a genuinely new axis in all frames.  The CD conjugation
`(a,b)* = (a*, −b)` is the iterated sign-swap (`neg_subNatNat`); the
per-doubling law-loss ladder (order → commutativity → associativity →
norm composition) is combinatorially derivable from the doubling
formula and is partially PURE in `Lib/Math/Algebra/CayleyDickson/`
(`CDDoubleMoufang`, `CDDoubleAlternative`, sedenion failure of
`TraceNormed213` lift).  Open brick 4: state the collapse-vs-rigid
criterion as a theorem schema (obstruction readout valued in old data
⟺ the pair quotient is total) connecting the completion square to the
CD tower.
