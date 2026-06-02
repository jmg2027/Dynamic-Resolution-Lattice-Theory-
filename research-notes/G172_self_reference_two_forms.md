# G172 — the two structural forms of self-reference, formalized (Bool-liar vs Nat-Lambek)

**Date**: 2026-06-02.  **Status**: closed ∅-axiom result.
**Source of truth**: `lean/E213/Lens/Bool213/SelfReferenceForms.lean` (2 PURE / 0 DIRTY).
**Anchors**: `seed/AXIOM/05_no_exterior.md` §5.2, `Lens/Bool213/Raw` (`not`, `not_not`,
`T_ne_F`), `Theory/Raw/Lambek` (`decompose`, `depth_drops`, `two_closures`).

## The thread

This branch's unique remaining axis (the real-number and Cayley-Dickson tracks are
elsewhere) is the **foundational / logic / residue** side of the original proposal.  A
survey found one clean, tractable, genuinely-open ∅-axiom target there: `05_no_exterior`
§5.2 describes two *structurally distinct* forms of the residue's self-reference, but only
the Nat-style side was formalized (Lambek), and the Bool-style "no fixed point" was stated
philosophically, never proved.

## What §5.2 says

The residue's self-reference admits two co-present realisations, read off the *same* Raw
self-pointing:

  - **Bool-style** (liar-like): `not` is its own inverse (`not_not r = r`, period 2) and
    admits **no fixed point** — oscillation, never grounding.
  - **Nat-style** (Lambek-like): the fixed-point combinator on inductive Raw produces
    actual closure — the iteration reaches its limit and stays (period-1 fixed point),
    well-founded.

The Bool-Lens extracts the oscillatory aspect (every distinguishing is a binary choice
that does not stand still); the Nat-Lens the cumulative aspect (every distinguishing
leaves a residue the next uses as input).  Same event, two readings.

## What was missing, and what is now closed

`Lens/Bool213/Raw` had the involution `not_not r = r` but **no** theorem that `not` has
no fixed point — the half that makes it the *liar* (period 2, never period 1).  Now:

  - **`bool_not_no_fixed_point`** (new): `∀ r, isBool r = true → not r ≠ r`.  On the Bool
    values `{T, F}`: `not T = F ≠ T` and `not F = T ≠ F` (from `not_T`/`not_F` + `T_ne_F`);
    off the values, `isBool` is `false`.  So the Bool negation never settles at period 1 —
    the oscillation is genuine, not just an involution.
  - **`self_reference_two_forms`** bundles the dichotomy as one ∅-axiom statement:
    Bool-style = involution (`not_not`) + no period-1 fixed point on its values
    (`bool_not_no_fixed_point`); Nat-style = period-1 self-fixed-point everywhere
    (`Lambek.decompose` — every Raw is its own constructor readout) + strictly
    well-founded slash descent (`Lambek.depth_drops`).

The contrast is now machine-checked: the Bool loop closes only at period 2 (oscillation,
no period-1 fixed point), the Nat loop closes at period 1 (identity, convergence) and
terminates at the atomic floor.

## The convergence-side re-entry made a theorem (`Lambek` §5)

The Nat-style side of the dichotomy was carried by the per-step facts (`decompose`,
`depth_drops`).  `Theory/Raw/Lambek.lean` §5 now states the **descent re-entry** as actual
well-foundedness — the dynamic form, and the convergence dual of the predicate-side
`Lens.ResidueReentry.residue_reentry_never_closes`:

  - `IsPart c p` — the **peel relation**: `c` is one of the two parts of a slash `p`.  One
    peel re-enters the structure at a part.
  - ★ `no_part_of_atom` — the atoms are **terminal**: nothing is a part of an atom (the
    floor where the descent stops).
  - ★ `part_depth_lt` — every peel re-enters strictly **shallower** (the measure).
  - ★ `isPart_wf` — **`WellFounded IsPart`**: every chain of peels terminates at an atom.
    Proof by strong induction on a `depth` bound (a part is shallower than its bound, so
    accessibility lifts one layer); ∅-axiom (`WellFounded`/`Acc` are Lean-core, the
    `DepthOmegaTower.coord_wf` pattern).
  - ★ `descent_reentry_converges` — bundles terminal-atoms + strict-descent +
    well-foundedness: the descent re-entry **converges** at the floor.

So the self-applying re-entry has two faces as one Raw self-pointing: read on the
atomic/Nat side (peeling toward the floor) it **closes** at the atoms (`isPart_wf`, bounded,
terminating); read on the predicate/residue side (re-pointing the encoded residue) it
**never closes** (`residue_reentry_never_closes`, unbounded, escaping).  This is the
re-entry analog of the `SpiralRotationInvariant` pairing (atomic conserves / residue
escapes) and the `DepthHeightDiagonal` ε₀-direction, now at the Lambek pointing floor.

## Honest scope

  - "No fixed point" is on the **Bool values** `{T, F}` (the Bool-Lens image), not all of
    `Raw` — `not = swap` does fix some general Raws.  That is the correct reading: the
    Bool-Lens reads only `{T, F}`, and there `not` is fixed-point-free, the liar.
  - The Nat-style side reuses the existing Lambek closure (`decompose`/`depth_drops`); the
    new content is the Bool half and the explicit dichotomy bundle.
  - This is a *facet* statement, not a claim that one form is "the" self-reference: both
    are co-present readings of one Raw self-pointing (§5.2, the View-as-facet discipline).

## Placement

`Lens/Bool213/SelfReferenceForms.lean` — downstream of both `Bool213` (Lens) and the Raw
public surface (`Theory.Raw.API`, which re-exports `Lambek`), so it can cite both without
reaching into a Theory.Raw submodule (the import-guard surface).  Registered in the
`Lens.Bool213` aggregator.

## Open (foundational/logic axis, still distinct from real / algebra tracks)

  - **ε₀ as the diagonal limit of the ordinal tower** — `DepthOmegaTower` closes `ω^r`
    (`coord_wf`); whether iterating the ceiling-diagonal (`DepthCeilingResidue.diag`)
    produces `ε₀` as a native limit (no Mathlib `Ordinal`) and coincides with the residue
    is the deeper open target (uncertain: the diagonal may bottom out at `ω^ω`).
  - **frozen = dynamic equivalence** — `φ` as `P`'s algebraic fixed point vs the Pell
    iteration limit are proven separately; an ∅-axiom theorem identifying them (§5.7)
    remains.
  - Computability / Church–Kleene is out of scope (a future Lens reading on top of the
    Nat-style recursion, not a current target).
