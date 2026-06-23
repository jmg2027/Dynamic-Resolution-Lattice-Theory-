# Universal Lens (G1 anchor)

**Status**: Closed (13 files).

## Overview

**The universal (canonical-form) Lens** — for any slash-congruence
`E` on Raw, `universalLens E` is the canonical Lens whose kernel is
exactly `E`.  It realizes the *slash-congruence → Lens-kernel*
direction: every Lens's distinguishing-equivalence is recovered as
the kernel of some `universalLens E`.  This is the **G1 anchor** —
universal-lens unification.

## Lean source

- `lean/E213/Lens/Universal/` (13 files), `QuotLens.lean` the core
- ∅-axiom PURE

## Narrative

Every Lens has a kernel — the slash-congruence identifying the Raws
it reads alike.  The **universal Lens** is the canonical
normalization map for a *given* congruence: `universalLens E : Lens
(Raw → Prop)` sends each Raw to its `E`-equivalence-class predicate,
so its kernel is exactly `E`:

  `universalLens_kernel_eq_E_R : (universalLens E).equivR r r' ↔ E r r'`.

It is **not** an injective / collapses-nothing Lens — its kernel is
`E`, whatever congruence `E` is.  The 13 files cover:

- **Construction**: `universalLens E : Lens (Raw → Prop)` — the
  canonical-form (normalization) map for the congruence `E`.
- **Kernel**: `universalLens_kernel_eq_E_R` — kernel = `E` exactly,
  stated on the distinguishing `equivR`-form (PURE).
- **Recovery (the universality)**: `universalLens_recovers_R` —
  every Lens `M`'s kernel is realized as `universalLens M.equiv`, so
  the construction is universal over congruences.
- **Idempotence**: `universalLens_idempotent_R` — normalizing twice
  is normalizing once.

So "realize a distinguishing-equivalence on Raw as a Lens kernel" is
a uniform construction: any such equivalence is the kernel of its
`universalLens`.

Note on the lattice: the **bottom** of the Lens-kernel preorder is
`idLens` (kernel = Raw equality — the finest distinction, collapsing
nothing), and the **top** is `constLens` (kernel = total — collapsing
everything; §6.5 / `RawTopology.lean`).  The universalLens is *not*
the bottom; it is the per-congruence normalization map.

## Connection

- `theory/lens/algebra.md` — kernel theory
- `theory/lens/lattice.md` — the Lens-kernel lattice (bottom = idLens, top = constLens)
- `theory/lens/compose.md` — factor-through definition
- `theory/lens/unified_equivalence.md` — universalLens realises the
  slash-congruence → Lens-kernel direction of the single concept.  The
  kernel is stated on the distinguishing `equivR`-form
  (`universalLens_kernel_eq_E_R`), which is PURE; the `=`-of-view form
  is retired (`theory/lens/dirty_recovery_patterns.md` Pattern P5).
