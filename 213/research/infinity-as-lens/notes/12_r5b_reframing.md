# 12 — R5b reframing via chain-space uncountability

## Original r5-critique framing

`research/r5-critique/notes/02_r5_vacuity.md` argued that R5b
("every non-terminating structural branch of `R` corresponds
to a uniquely determined state in α") quantifies over objects
**outside** the inductive Raw type — the "non-terminating
branches" are coinductive streams, not Raw terms.  The note
concluded R5b **smuggles classical infinity** (coinductive
extension of Raw, or set-theoretic branch completion) into
the Lens framework.

## Refinement via Σ3 + Σ5 + Σ6 + Chain

Sessions 1–5 of `infinity-as-lens` put several things in
place that sharpen the picture:

- **Σ3** (`raw_at_least_countable`): Raw has at least
  ℕ-many elements via the explicit `rawTower`.
- **Σ5** (`cantor_general`): no surjection `X → (X →
  Bool)` for any `X`.
- **`chain_uncountable`** (this note's new theorem):
  no surjection `ℕ → (ℕ → Raw)`.

The **chain-space** `ℕ → Raw` = infinite sequences of Raw
terms = the natural Raw-internal candidate for "non-
terminating branches".  And by the new Lean theorem it is
**uncountable** (strictly larger than `ℕ`, hence strictly
larger than Raw).

## What this does to the old "smuggling" claim

The original claim had two components:

1. *R5b quantifies over objects not in Raw.*
2. *Hence R5b is external / smuggled.*

(1) is still correct — chains are **functions on** Raw, not
elements of Raw.  But (2) is **now weakened**: the *cardinality
demand* of R5b (that α be "large enough" to receive each
chain as a distinct limit-state) is supported by a
**Raw-internal theorem** (`chain_uncountable`).

So:
- The **cardinality** side of R5b is Raw-internal.
  (Chain-space is uncountable, and this is proved without
  leaving Lean 4 core.)
- The **limit-state / convergence** side of R5b (that each
  chain has a unique well-defined *limit* in α) still imports
  a notion of Cauchy-completeness that is external to Raw.

## Refined interpretation

R5b has the structure:

  ∀ chain in `ℕ → Raw`, ∃ α-state uniquely determined.

The chain-side is **internal** (`ℕ → Raw` is a Lean type, its
uncountability is `chain_uncountable`).  The "uniquely
determined" state-side requires the **codomain** α to have
Cauchy-completeness — a topological / analytical notion that
enters as an *additional* axiom on α, not as a property of Raw.

So the cardinality bottleneck forcing `|α| ≥ 𝔠` is Raw-internal
(pigeonhole between chain-space cardinality and α's image).
The specific choice of **which** 𝔠-sized structure (namely
ℝ rather than, say, ℝ_alt, 2-adic completions, etc.) depends
on the external completeness axiom and on continuity.

## Status of the original "smuggling" claim

**Half right, half updated**:
- R5b's cardinality demand ≥ 𝔠: Raw-internal (now formal).
- R5b's specific limit-state structure (Cauchy complete,
  archimedean, minimal): still external analytic axioms.

This is a finer distinction than the original r5-critique
made, and better supported by the Lean-side formalisation.

## What this means for Paper 2

If Paper 2 is to argue "R5b smuggles classical infinity",
the correct claim is **narrower**: R5b's
*completeness-and-uniqueness-of-limit-state* structure is
non-Raw-internal.  The cardinality demand itself is
Raw-internal.

This may *weaken* Paper 2's claim but *clarify* it: the
paper's R5b contains one axiom-external kernel (complete-
ness / uniqueness), not the whole condition.  The
cardinality half is defensible.

## Lean citation

Theorem: `E213.Infinity.chain_uncountable`
File: `framework/E213/Infinity/Chain.lean`
Proof: Cantor diagonal using `Raw.a ≠ Raw.b` to generate a
"different from f n n" chain.

Connects to the rest of the Σ program:
- Σ3 (Raw ≥ ℕ) + Σ5 (X → Bool uncountable) give cardinality
  infrastructure.
- Chain uncountability is the natural "R5b cardinality"
  consequence.
