# 17 — Existence mode is a Lens output (2026-04-24)

## The question (Mingu's formulation)

> "Is the 213 space already there, or is it being built
> inductively?  My claim is: don't care — the axiom
> does not say, and it doesn't matter.  (I think this
> can be proved.)"

## The claim

The Raw axiom does **not** judge whether Raw's terms are
"already existent" (Platonic reading) or "being generated"
(constructive / potentialist reading).  Both readings are
models of the axiom.  The distinction is itself a **Lens
output**, parallel to how cardinality is a Lens output
(Σ4).

This is not methodological shrugging.  It is a claim about
what the axiom *can* say, and it admits formalisation.

## Why the axiom does not judge existence mode

The axiom has three clauses:
1. `a` is a Raw term.
2. `b` is a Raw term.
3. If `x` and `y` are Raw terms, so is `x ⋄ y`.

No clause asserts "every possible Raw term exists
simultaneously" (Platonism).  No clause asserts "Raw terms
come into being one step at a time" (constructivism).  The
axiom is silent.

## Every Σ-theorem is existence-mode-neutral

Scan of `framework/E213/Infinity/`:

- `rawTower_injective` (Σ3): for every `n : ℕ`, an
  explicit finite witness.  Compatible with both readings.
- `Raw.toNat_injective` (Σ2): per-term Gödel number.
  Compatible.
- `cantor_raw_bool` (Σ5): proof refers to function space,
  not to any enumeration of Raw.  Compatible.
- `chain_uncountable`: diagonal on `ℕ → Raw`, no
  existence-mode choice needed.
- `raw_equipotent_nat`: a bijection-on-witnesses claim,
  not a "both collections exist" claim.

**No Σ-theorem in `Infinity/` requires either reading.**

## Relationship to Σ4

Σ4 (in `LensCardinality.lean`) showed that cardinality is
Lens-output: boolAnd gives image-size 1, parity gives 2,
leaves gives ℕ, function-space lens gives uncountable.

**Claim of this note**: *the existence mode of Raw is
analogously Lens-output.*  Axes:

| Lens                  | Existence mode emitted |
|-----------------------|------------------------|
| Platonic completion   | all terms simultaneous |
| Step-induction Lens   | terms generated stepwise |
| Potentialist Lens     | only already-constructed terms "exist" |
| Cofinite-window Lens  | any specific term exists after some step |

Just as the same Raw emits image sizes 1, 2, ℕ, 𝔠 under
different Lenses, the same Raw emits "already existent"
vs "being generated" under different metaphysical Lenses.
The axiom itself is orthogonal to this axis.

## What "don't care is provable" means

Two interpretations, both defensible:

**Weak — independence.**  Neither "Raw has all terms
simultaneously" nor "Raw terms are generated stepwise" is
derivable from the axiom + Σ theorems.  Both are
consistent extensions.  This is standard model-theoretic
independence and could be made precise by exhibiting two
non-isomorphic models, one for each reading.

**Strong — DRLT-style.**  The question "are Raw terms
already there?" is only meaningful once an existence-mode
Lens is specified.  Absent a Lens, the question is a
type error, not an open problem.  This parallels Σ4's
cardinality story.

The strong version is more in line with the Raw+Lens
programme: foundational questions that appear to be about
Raw turn out, on inspection, to be about the Lens chosen
to read Raw.

## Lean opportunity

A `framework/E213/Infinity/ExistenceModeLens.lean` would:
1. Define two target types `PlatonicExistence`,
   `StepwiseExistence` with distinct semantics.
2. Exhibit two Lens-like observations from Raw into each.
3. Show that no Σ-theorem distinguishes them.

Skeleton estimate: one session.  Not prerequisite for any
current theorem but would close the philosophical loop
formally.

## Why this matters (sessions wasted)

- Earlier sessions repeatedly re-opened "but is Raw
  actually a finished object?"  Every time, the answer
  converges on "don't care" but takes 20–40 min to
  re-derive.
- The r5-critique arc spent time on whether "R5b smuggles
  classical infinity".  Note 12 reframed it as
  Raw-internal cardinality; the existence-mode axis is
  a second, independent reframing target.

Recording this once, here, should prevent recurrence.
