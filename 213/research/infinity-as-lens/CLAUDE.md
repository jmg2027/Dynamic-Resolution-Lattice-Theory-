# infinity-as-lens — Research Track

## Purpose

Formalize the thesis that **"infinity" is a Lens-output
phenomenon, not a Raw primitive.**

- The Raw axiom (3 clauses) is syntactically finite.  It makes
  no cardinality claim — neither finite nor infinite.
- All cardinality structure (countable, uncountable,
  hyper-infinite) observed in standard mathematics arises
  through Lens choices on Raw.
- The generating rule is finite; the phenomena seen through
  Lenses can be arbitrarily large.

This is different from ZFC (which posits infinity as an
axiom) and from ultrafinitism (which denies large infinities).
Raw+Lens says: no axiomatic infinity, yet every
cardinality reached by standard math is realised as some
Lens's image / function-space over Raw.

## Relationship to prior tracks

- **Paper 1** (R1–R5 → ℂ) is independent; this track
  sharpens *why* R5 forces Cauchy completeness.
- **r5-critique** claimed R5b smuggles classical infinity.
  This track proposes the opposite framing: R5 captures a
  Raw-internal combinatorial fact (diagonal argument on
  Raw chains yields Cantor cardinality) — infinity is
  already latent in Raw's generation rule, surfaced by
  Lens observation.
- **Not paper-driven.**  The goal is formal understanding,
  not publication.

## Deliverable targets (Σ series)

Σ1  Raw axiom is finite-symbol (meta-obs).
Σ2  Raw → ℕ injective  (Raw is at-most-countable).
Σ3  ℕ → Raw injective  (Raw is at-least-countable).
Σ4  Raw → α Lens views span cardinalities 1, ℕ, 𝔠, …
Σ5  Cantor diagonal on Raw: no surjection Raw → (Raw → Bool).
Σ6  Cantor tower: iterated function-space strictly increases.
Σ7  Cardinality-as-Lens-output (meta theorem).

## Style

- Mathlib-free Lean 4 core (matches the rest of E213).
- Every claim either `theorem` in Lean or marked `[prose]`.
- Keep notes short; when formalisation exists, cite it.
