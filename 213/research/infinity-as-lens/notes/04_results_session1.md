# 04 — Results: session 1 Lean output

All proofs 0 `sorry`, 0 `axiom`, Mathlib-free, `lake build` ✓.

## What was proven

**Σ3** — `∃ f : ℕ → Raw, Function.Injective f`.
- File: `framework/E213/Infinity/Countable.lean`.
- Construction: `rawTower n` = right-leaning tree
  `a / (a / (a / ... / b))` with `n` slashes.
- Proof: leaves of `rawTower n` = `n + 1`; distinct `n`
  give distinct leaf counts, hence distinct Raws.
- Packaged as `raw_at_least_countable`.

**Σ5** — `¬ ∃ f : Raw → (Raw → Bool), Function.Surjective f`.
- File: `framework/E213/Infinity/Cantor.lean`.
- Proof: Cantor diagonal.  Given candidate surjection `f`,
  the function `g r := ! (f r r)` differs from every `f k`
  at position `k`.
- Also proved in generic form: `cantor_general {X : Type}`.

**Σ6** — Cantor tower three layers up:
- `tower_0_1 : ¬ ∃ f : Raw → (Raw → Bool), surj f`   (= Σ5)
- `tower_1_2 : ¬ ∃ f : (Raw→Bool) → ((Raw→Bool)→Bool), surj f`
- `tower_2_3 : ¬ ∃ f : L2 → L3, surj f`
- Each just instantiates `cantor_general`.
- File: `framework/E213/Infinity/Tower.lean`.

## What this says, mathematically

1. Raw's generation rule is finite (3 constructors, each
   first-order).  **Lean sees the axiom as finite data.**

2. Yet Raw has at least ℕ-many elements (Σ3): the tower
   gives a concrete injection `ℕ ↪ Raw`.

3. The function space `Raw → Bool` is strictly larger than
   Raw (Σ5): no surjection exists.  By Cantor, this space
   is uncountable — strictly more than ℕ.

4. The cantor tower climbs further (Σ6): each layer is
   strictly larger than the previous.  Three layers
   formalised.  More layers via the same
   `cantor_general` theorem.

## What the thesis gains

The originator's claim: "cardinality is a Lens-output
phenomenon, not a Raw-intrinsic one."  This session's
Lean output exhibits it concretely:

- *Lens-independent fact* about Raw: it is at least
  ℕ-sized (Σ3).  Fair — Raw's inductive structure forces
  countable generation.

- *Lens-dependent / observation-dependent facts*: the
  function-space hierarchy `Raw → Bool → Bool → …`
  climbs Cantor's ladder.  Each step is an
  observation (a choice of higher-order codomain),
  not a Raw primitive.

So Raw's ontology (what exists) is ℕ-sized.  Its
*epistemology* (what we can extract via Lens-style
observation) reaches any cardinality Cantor can name.
**The gap between the two is the content of "infinity is
Lens".**

## What's left

- **Σ2** (Raw → ℕ injection) — not yet formalised;
  argued at prose level.  Combined with Σ3 would give
  `Raw ≈ ℕ` bijection (classical countability).  Would
  require Gödel-encoding Tree → ℕ + injectivity proof.
  Deferred.

- **Σ4** — explicit Lens-image cardinality table.
  The catalogue from session 1 (ParityLens, signedLens,
  ZSqrt D) already populates some rows; Σ4 is a
  write-up / consolidation task.

- **Σ7** (meta-theorem cardinality = Lens output) —
  requires prose + metatheoretic care.  Basis is in
  place from Σ3 + Σ5 + Σ6.

- **Cayley–Dickson formalisation** — see
  `notes/03_cayley_dickson.md`.  Needs a future session.
