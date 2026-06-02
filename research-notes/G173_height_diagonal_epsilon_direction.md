# G173 — naming the ω^r height-tower escapes every finite height (the ε₀-direction)

**Date**: 2026-06-02.  **Status**: closed ∅-axiom result.
**Source of truth**: `lean/E213/Lib/Math/Cauchy/DepthHeightDiagonal.lean` (4 PURE / 0 DIRTY).
**Anchors**: `Cauchy/DepthOmegaTower` (`expTower`, `coord_layer_dominates`, `coord_wf`),
`Cauchy/DepthCeilingResidue` (`diag`, `diag_not_in_seq`, `cantor_general`),
`seed/AXIOM/05_no_exterior.md` §5.1–5.2.

## The target and the honest scope

The foundational/logic axis had one deep open item: the ε₀-direction — whether
diagonalising the `ω^r` ordinal tower produces the next ordinal step.  The survey flagged
this as uncertain: constructing ε₀ as an ordinal object (no Mathlib `Ordinal`) is a large,
possibly-forced task.  So the honest, ∅-axiom-shaped version is *not* "construct ε₀" but
the structural fact underneath it: **naming the whole height-tower escapes every finite
height** — the residue read at the scale of the tower's height.

## What is closed

`DepthOmegaTower` gives the `ω^r` ladder (`coord_wf`, each height well-founded;
`coord_layer_dominates`, each layer ×`ω`) and the sequence side `expTower c r`
(`expTower c (r+1) = c^{expTower c r}`).  `DepthCeilingResidue` gives the diagonalisation
`diag f n = f n n + 1` that escapes the sequence it summarises (`diag_not_in_seq`, the
Cantor self-cover).

`DepthHeightDiagonal` applies the diagonalisation to the **height index**:

  - `heightTower c r n = expTower c r n` — the height-tower as a two-argument family
    (height `r`, sequence index `n`), exactly the shape `diag` consumes;
  - `heightTower_diag`: `diag (heightTower c) r = expTower c r r + 1` (the diagonal value);
  - ★ `height_diagonal_escapes`: `∀ r, diag (heightTower c) ≠ expTower c r` — naming "all
    the heights `ω^r` at once" is **not** any finite-height tower.  Every attempt to name
    the whole ladder lands one step beyond every finite `ω^r` — the `ω^ω` ceiling — and
    naming *that* is the next step again;
  - ★★ `epsilon_direction`: bundles `coord_layer_dominates` (each height layer ×`ω`, so
    the `ω^r` heights have no top finite level) with `height_diagonal_escapes` (naming the
    whole ladder escapes every finite height).

## Reading

This is the residue (`DepthCeilingResidue`) at the scale of the tower's *height*, one
scale up from the sequence-level diagonalisation: the `ω^r` ladder has no top, and naming
the ladder reproduces the Cantor self-cover.  It is the structural content of the
open-ended "diagonalise the tower height" step — the frontier *toward* `ε₀`.

**Honest:** no `Ordinal` object is constructed and `ε₀` is *not* claimed to be reached.
`ε₀` is the classical ordinal reading of this open-endedness (the supremum of the `ω^r`
ladder, then named); here only the ∅-axiom structural fact (the diagonal escapes every
finite height) is proved.  Whether a native `ε₀` object exists in this framework remains
open and is not forced by this result.

## Open (this axis)

  - A native `ε₀`/limit-ordinal object (no Mathlib `Ordinal`) and a proof that the
    height-diagonal is its `+1` — genuinely uncertain (the diagonal may only express the
    `ω^ω` ceiling, not a canonical `ε₀`).
  - frozen = dynamic equivalence (§5.7): `φ` as `P`'s algebraic fixed point vs the Pell
    iteration limit, identified by one ∅-axiom theorem.
  - Computability / `ω₁^CK`: out of scope (a Lens reading on top of Nat-style recursion).
