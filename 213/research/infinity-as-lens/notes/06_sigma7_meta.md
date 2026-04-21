# 06 — Σ7: Cardinality is Lens-output (meta)

Consolidating the formal results into a single meta-statement.

## The claim

**The Raw axiom is silent on cardinality; every cardinality
fact observed in standard mathematics arises via Lens-style
observation of Raw, not from the axiom itself.**

More precisely:
1. The axiom's generation is *finite syntax* (three
   constructors: `a`, `b`, `slash`).
2. Raw-intrinsic cardinality is exactly `ℕ` — no more, no
   less.
3. The function-space hierarchy over Raw (Lens views into
   `Bool`, then `Raw → Bool → Bool`, …) climbs Cantor's
   ladder with no upper bound.
4. Consequently, arbitrarily high cardinalities are
   reachable as *observations* of Raw, while the generating
   system contains no cardinality postulate.

## Formal citations

All packaged in `E213.Infinity.LensCardinality.sigma7_cardinality_is_lens_output`:

```
theorem sigma7_cardinality_is_lens_output :
    (∃ g : Raw → Nat, Injective g)              -- Σ2
    ∧ (∃ f : Nat → Raw, Injective f)             -- Σ3
    ∧ (¬ ∃ h : Raw → (Raw → Bool), Surjective h) -- Σ5
    ∧ (∀ X : Type,
         ¬ ∃ k : X → (X → Bool), Surjective k)   -- generic
```

Individual components by Lean name:
- Σ2 `E213.Infinity.raw_at_most_countable`
      (via `Raw.toNat_injective` + Gödel numbering).
- Σ3 `E213.Infinity.raw_at_least_countable`
      (via `rawTower_injective` + right-leaning tower).
- Σ5 `E213.Infinity.cantor_raw_bool`
      (specialisation of `cantor_general`).
- Σ6 `E213.Infinity.tower_0_1`/`tower_1_2`/`tower_2_3`
      (Cantor tower three explicit rungs).
- Σ4 `E213.Infinity.leaves_surjective_pos`,
      `depth_surjective`, `signedLens_image_ge_neg_one`,
      `maxLens_image_binary`, `boolAndLens_image`, …
      (Lens-image cardinality data).

## What this says, mathematically

Raw is a single, very small object: the free commutative
magma on two generators with no fixed points.  Its elements
are in bijection with ℕ.

When we ask "what does Raw look like to an observer?", we
choose a Lens — a codomain `α` with `base_a, base_b,
combine` — and see the image under `Raw.fold`.  The image
can be:

- a singleton (`boolAndLens` — the observer cannot
  distinguish anything),
- a two-element set (`parityLens`, `maxLens` — the
  observer sees a single bit),
- a countable unbounded set (`Lens.depth`, `Lens.leaves`,
  `signedLens`, the `ZSqrt D` family — the observer
  reconstructs countable-rank arithmetic),
- an uncountable set (lifting to function spaces `Raw →
  Bool`; Cantor shows no surjection from Raw recovers
  it).

Iterating the function-space construction climbs Cantor's
ladder indefinitely.  Every cardinality standard
mathematics uses *below* the full set-theoretic class
structure is reachable this way.

## What this does NOT claim

- **Not**: Raw encodes every mathematical structure.
  Category-theoretic constructions (limits, Kan extensions),
  higher-arity algebras, and subset/quotient structures in
  general require richer-than-Lens observations.  The
  Lens layer is a specific subclass.
- **Not**: Gödel's incompleteness is bypassed.  The
  phenomena relocate to particular Lenses (e.g. a Lens
  that encodes PA inherits Gödel's limitations as
  properties of that Lens, not of Raw).
- **Not**: "Infinity doesn't exist".  The mathematician's
  routine infinities are *visible* through Lens
  observation.  They simply are not *stipulated* by the
  Raw axiom.

## Status vs the originator's thesis

Mingu's original claim — *cardinality is Lens-output, not
Raw-intrinsic* — is formally supported by Σ2 + Σ3 + Σ5 +
Σ6 + Σ4, with the caveat that:
- Raw-intrinsic cardinality IS `ℕ` (not zero); the claim
  holds in the sense that no cardinality *beyond* ℕ is
  Raw-intrinsic.
- "Potential infinity" (the unbounded inductive generation)
  is Raw-intrinsic in the constructive sense; "completed
  infinity" and higher cardinalities are Lens-side.

The distinction between potential and completed infinity
is the refinement the Lean formalisation adds to Mingu's
initial claim.

## Next

- Cayley–Dickson doubling (notes/03) as a concrete
  parametric Lens-image family ascending dimensionally
  (ℤI → Hurwitz → Cayley) — a structural, not just
  cardinality, extension of Σ4.
