# `Lens/Instances/` — Concrete Lens catalog

Concrete `Lens α` instances for specific α codomains.  Each file
provides one or more concrete Lens — useful as building blocks for
downstream constructions.

## Inventory (~25 files)

By codomain category:

**Bool-valued** (decision lenses):
  - `AB.lean`, `Bool.lean`, `CompoundBool.lean`, `And.lean`,
    `Or.lean`, `Xor.lean`

**Nat-valued** (counting/measurement lenses):
  - `Identity.lean`, `Inv.lean`, `ListMax.lean`, `Max.lean`,
    `MaxByLeaves.lean`, `MinByLeaves.lean`

**Finite-valued** (modular/parity lenses):
  - `F9.lean`, `Mod.lean`, `ModN.lean`, `Parity.lean`,
    `ZMod6.lean`

**Path-valued** (structural lenses):
  - `Path.lean`, `Sym.lean`

**Cauchy-derived** (analysis-flavored):
  - `Cauchy.lean`

**Reach** (image-construction infrastructure):
  - `Reach.lean`

**Funext-refactor pattern lenses** (G12 Tier 3 F2, parts 1-15):
  - `PointwiseProjection.lean` — function → query stream lens
  - `EndpointBehavior.lean` — function → endpoint pair lens
  - `BoundedContext.lean` — bounded query window lens
  - `CochainEntry.lean` — cochain → per-entry lens
  These formalise the implicit lens choices that distinguish
  pointwise PURE views from function-eq DIRTY views in Real213
  + Cohomology.

## Public API

NOT bundled in `E213.Lens.API` shim.  Import individually:
```
import E213.Lens.Instances.Bool
import E213.Lens.Instances.Path
```

## Future organisation (G12 §6.3 S2 recommendation)

When the catalog grows beyond ~30 entries, sub-cluster by codomain
category:
  - `Instances/Bool/`
  - `Instances/Nat/`
  - `Instances/Finite/`
  - `Instances/Structure/`

## Where to add new Lens instances

Match by codomain.  If new codomain category, create new file (or
sub-cluster if multiple files would share it).
