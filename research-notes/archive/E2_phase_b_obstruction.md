# E2 — Raw-realization obstruction in Phase B (Arithmetic)

## Discovery (2026-04-26)

The following obstruction found while attempting Phase B1 (Real213
addition).

## Image of abLens.view

`abLens_surjective` from `framework/E213/Research/PellSeq.lean`:

```
∀ a b : Nat, a + b = s → 1 ≤ a → 1 ≤ b → ∃ r : Raw, abLens.view r = (a, b)
```

**Precise description of the image**:

```
range(abLens.view) = {(1, 0)} ∪ {(0, 1)} ∪ {(a, b) : a ≥ 1 ∧ b ≥ 1}
```

Evidence:
- (1, 0): view of Raw.a.
- (0, 1): view of Raw.b.
- (a, b), a ≥ 1, b ≥ 1: abLens_surjective.
- (0, k) for k ≥ 2: **no realizable Raw** — slash requires distinct
  → cannot assemble from b-leaves only.
- (k, 0) for k ≥ 2: absent for the same reason.

## Addition obstruction

view of a/b + a'/b' = (a*b' + a'*b, b*b').

Key obstruction case: two sequences simultaneously accumulate
"0-counts", producing b-count ≥ 2 in the sum view.  Example:
(0, 1) seq + (a, b≥1 with a=0) seq → no boundary.

## True issue

Raw's view image is restricted in a *precise* form.  Since Real213's
sequences are built from Raw only, the view is in the image.  But *the
sum's view also* must be in the image to be liftable to Real213.

Is the sum image *always* closed within the range? — **No.**
(1, 0) + (1, 0) = (0, 0) is the boundary case (Raw.a + Raw.a,
"infinity + infinity").

## Solution candidates

### (i) Real213StrictPos: all views are (a, b) with a, b ≥ 1

```
structure Real213StrictPos extends Real213 where
  view_pos : ∀ i, (abLens.view (xs i)).1 ≥ 1 ∧
                  (abLens.view (xs i)).2 ≥ 1
```

Addition is well-defined on this subtype:
- (a, b), (a', b') with a, b, a', b' ≥ 1 → sum view = (a*b' + a'*b,
  b*b') with both ≥ 1, abLens_surjective possible.

### (ii) Equivalence-class addition (defer)

View Real213 as equiv-classes and choose the *representative* of
arbitrary r as the strict positive view.  More abstract.

## Decision

**(i) recommended** — most concrete, framework-internal, no axiom
addition.  Phase B work proceeds on `Real213StrictPos`, with separate
work later for cut-equivalence compatibility of
`Real213StrictPos → Real213`.

## Falsifiability meaning

Is this obstruction a *framework boundary*?

- **NO**: addition itself is possible within the framework — only a
  *type refinement* is needed (StrictPos).  A workaround exists.
- *No hidden axiom addition* — all work is framework-internal.

Therefore not a falsifiability trigger — a simple *engineering
challenge* (type refinement).

## E1 roadmap update

- All milestones of Phase B are work on `Real213StrictPos`.
- Phase A addition:
  - A6 (proposed): `Real213StrictPos` subtype definition + Real213 ↔
    StrictPos cut-equivalence compatibility.

## Next

After adopting E2's decision, work on `Real213StrictPos.lean` +
`Real213Add.lean`.
