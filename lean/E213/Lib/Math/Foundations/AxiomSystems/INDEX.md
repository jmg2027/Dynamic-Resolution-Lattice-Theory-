# `Math/AxiomSystems/` — Classical foundations as lens compositions on Raw

★★★ **G12 Tier 5 (C1-C4) ENDGAME demonstration** ★★★

Different mathematical theories — even axiom systems — are
combinations of Lenses (different mathematical theories, even axiom
systems, are combinations of Lenses).

Critically: 213's Raw is **forced uniquely** (Atomicity proofs).
There is NOT a "choice" of Raw bases.  All classical foundations
(ZFC, Peano, classical analysis, ...) are different **Lens
compositions reading the same Raw residue**.

This sub-cluster makes that picture concrete with small Lean
demonstrations.

## Files

  - **`PeanoAsLensComposition.lean`** — Peano arithmetic emerges
    from Raw via successor-lens composition
  - **`ZFCExtensionalityAsLens.lean`** — ZFC extensionality as
    a particular lens collapse
  - **`ClassicalAnalysisCompletenessAsLens.lean`** — completeness
    as composite lens
  - **`CrossTheoryCohabit.lean`** — single Raw expression
    viewable simultaneously as ZFC theorem + Peano theorem

## Honest scope

These are **demonstrations**, NOT full axiomatic theory ports.
The full claim — "all of mathematics derives from Raw + lens
compositions" — is a multi-decade research program.

What we provide here:
  1. The **structural commitment**: each classical foundation is
     a particular Lens (Raw → α) where α is the foundation's
     primitive type
  2. **Small witnesses**: a few representative theorems shown to
     hold under each lens choice
  3. **Concrete demonstration of cohabitation**: a single 213
     Raw expression yields valid theorems in multiple classical
     foundations simultaneously

## Connection to research notes

  - **G3** (Raw as universal trajectory space): the formal
    statement that every classical theory's foundation factors
    through Raw via some Lens
  - **G6** (Hodge translation): the demonstration that
    standard mathematics' "redundant ZFC packaging" hides simpler
    finite combinatorial content visible in 213
  - **G11** (Galois at eighty): the historical-philosophical
    thesis that structural foundations naturally precede ZFC

## Connection to AxiomLenses/

`Lens/AxiomLenses/{Propext, Funext, QuotSound}.lean`
formalises the *Lean kernel axioms* as lens choices.  This
sub-cluster (`Math/AxiomSystems/`) goes one level higher: entire
**axiom systems** (foundations) as lens compositions.  The two
together complete the picture.
