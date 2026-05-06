# `Hypervisor/Lens/Kernel/` — Lens-kernel theory (internal)

Internal theory about *Lens kernels* (the equivalence relation
`Lens.equiv`): congruence, correspondence, free audits, four-distinct
witness construction.

These are infrastructure for HV3 (Initiality) and HV6 (Universal
Form), not directly consumed by App or downstream code.

## Files (8)

  - `Congruence.lean` — Lens-kernel is a congruence on Raw
  - `Corresp.lean` — Lens-kernel correspondence theorems
  - `FreeAudit.lean` — free-magma audit of Lens kernels
  - `FourDistinct.lean` — four-distinct-Raw witness for
    Lens-injectivity proofs
  - `IdLensEq.lean` — identity Lens kernel = `Eq`
  - `Space.lean` — Lens-kernel space structure
  - `SwapInvariant.lean` — swap-invariant Lens characterisation
  - `CardinalityLB.lean` — Lens-kernel cardinality lower bounds

## Public API

Sealed (NOT API).  These support HV3/HV6 (initiality + universal
form) but are not exported by `E213.Lens.API`.

## Where to add new kernel-theory facts

  - About Lens.equiv → `Congruence.lean`, `Corresp.lean`
  - About Lens injectivity → `FourDistinct.lean`,
    `CardinalityLB.lean`
