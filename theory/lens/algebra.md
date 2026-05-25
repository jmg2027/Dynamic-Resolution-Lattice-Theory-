# Lens Algebra — Kernel Theory

**Status**: Closed (3 files).

## Overview

**Internal theory about Lens kernels** — the equivalence relation
`Lens.equiv`: congruence, correspondence, free audits, four-distinct
witness construction.

The Lens kernel = the equivalence classes that a Lens produces on Raw.

## Lean source

- `lean/E213/Lens/Algebra/` (3 files)
- ∅-axiom PURE

## Narrative

Each Lens `L : Raw → α` partitions Raw into equivalence classes
(`L.equiv r r' ↔ L r = L r'`).  Lens Algebra characterises the
kernel relation:
- **Congruence**: Lens.equiv is a congruence wrt Raw's substrate ops
- **Correspondence**: kernel partition ↔ Lens up to isomorphism
- **Four-distinct witness**: explicit Raw quadruples that the kernel
  must NOT collapse (used in distinctness proofs)

## Connection

- `theory/lens/universal.md` — universal Lens has minimal kernel
- `theory/lens/lattice.md` — kernel-refinement = `refines` preorder
- `theory/lens/unified_equivalence.md` — kernel theory as one
  reading of the Lens-arrow (the single concept covering
  equivalence / equivalence-class / isomorphism / homomorphism)
