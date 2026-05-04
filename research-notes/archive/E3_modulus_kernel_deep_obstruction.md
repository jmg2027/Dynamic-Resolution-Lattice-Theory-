# E3 — Deep obstruction in the ModulusCombiner kernel

## Building the kernel (2026-04-26)

`Real213ModulusCombiner.lean`: abstract kernel completed.

```
structure ModulusCombiner (combine : Raw → Raw → Raw) where
  precX : Nat → Nat → Nat × Nat
  precY : Nat → Nat → Nat × Nat
  precX_k_pos / precY_k_pos
  preserves : ... — orderProj match propagation
```

`combineModulus` generic theorem: two HasModulus + ModulusCombiner →
combined HasModulus.  Cauchy bookkeeping isolated to *one place*
([propext] only).

## Trivial instances ✓ (kernel validation)

- `piOneCombiner` : combine x y = x (0 axioms).
- `piTwoCombiner` : combine x y = y (0 axioms).
- `constCombiner c` : combine = constant c (0 axioms).

These 3 instances confirm the well-formedness of the kernel.

## Deeper obstruction for addition

When attempting an addition combiner, a *fundamental* problem is found:

**Insufficient information from a single-precision query**.

The `preserves` of ModulusCombiner: x1, x2 match orderProj at
*single* precision (m_x, k_x), y1, y2 match at *single* precision
(m_y, k_y) → combined matches at (m, k).

Addition: orderProj of sum view (a*b' + a'*b, b*b') at (m, k) =
decide ((a*b' + a'*b)*k ≤ b*b'*m).  This decision depends on the
*exact values* of (a, b, a', b') — not decidable from cut decisions
at single precision only.

**Counterexample**: x1 view (1, 2), x2 view (2, 4) — both ratio 1/2.
orderProj 1 2 of (1, 2) = decide(2 ≤ 2) = true.  orderProj 1 2 of
(2, 4) = decide(4 ≤ 4) = true.  Single precision match.

But sum with y view (1, 1): sum1 view = (1*1 + 1*2, 2*1) = (3, 2),
sum2 view = (2*1 + 1*4, 4*1) = (6, 4).  Both ratios are 3/2 —
orderProj matches OK at any (m, k).  Fortunately they are the same.

Hmm — *this specific case* is OK since the ratios are equal.  But in
general, when the *values* of views differ, the match of orderProj
only guarantees *cut-side* equality, not view-equality.

## True issue

The view of a Cauchy sequence does not stabilize to a *value* —
only the orderProj *decision* stabilizes.  The orderProj of the
sum view for addition depends on the *value-pair* of the view.
The sum decision cannot be determined from the decision-side alone.

## Possible resolution directions

### (A) Multiple-precision queries

Extend ModulusCombiner: precX is a *list* of precisions rather than
single precision.  213 form of Bishop's ε/2 trick — narrow the sum
decision by combining multiple cut decisions.

```
structure ModulusCombiner (combine) where
  precX : Nat → Nat → List (Nat × Nat)
  preserves : ... ∀ p ∈ precX, orderProj p of x1 = of x2 → ...
```

This design is more expressive.  But *how many precisions* are needed
is case-specific.

### (B) Stronger Cauchy form — bounded view variation

Extend HasModulus: guarantee not just the stability of orderProj but
also the *bounded variation* of the view-value.

```
structure StrongModulus where
  N : Nat → Nat → Nat
  cauchy_at : ...  -- orderProj
  view_bound : ∀ ε > 0, ∃ N, ∀ i j ≥ N, |view i - view j| < ε
```

With this form addition is natural — Bishop's standard.  But no
compatibility with *existing* HasModulus — need to re-prove instances
for Pell, Diagonal, etc.

### (C) Cut-level addition

Define addition directly on `RealCut := Nat → Nat → Bool`.
However, ∃-quantifier-heavy.  No decidability.

## Decision

**(B) recommended** — consistent with Bishop's ε-N standard, no
external axioms.  Strengthen HasModulus to a *strict* form + re-prove
existing instances.  This is a genuinely long arc.

Or (A): more abstract, but requires case-specific tuning.

## Falsifiability

This obstruction is also an *engineering challenge* — Bishop's program
itself works (external mathematics literature), simply a matter of
*choosing the right abstraction* within 213.

## Next

- **F1 (proposed)**: `StrongModulus` typeclass + re-proof of existing
  instances (Pell, Diagonal).
- **F2 (proposed)**: ModulusCombiner kernel on `StrongModulus`.
- **F3 (proposed)**: Addition instance.

A separate large arc — this session only reaches *diagnosis*.
