# `Hypervisor/Lens/Leaves/` — Leaves-flavored Lens facts

Lens-theoretic facts that focus on the *leaves* (number of
base-element occurrences) view.  Includes parity, mod-N
characterisations, and depth/leaves comparisons.

## Files (5)

  - `DepthIncomparable.lean` — depth and leaves are incomparable
    Lens characterisations (neither refines the other)
  - `DepthJoin.lean` — depth-join characterisation
  - `Mod3.lean` — leaves modulo 3 lens
  - `ModNat.lean` — leaves modulo arbitrary Nat lens
  - `RefinesParity.lean` — parity-related refinement
    [⚠ pre-existing build error: bf34de0 — unknown namespace
     `E213.Meta`; needs fix; not in API shim until fixed]

## Public API

Mostly internal.  `Mod3`, `ModNat` are concrete Lenses
catalogued in HV7 (Instances); the others are property theorems
in HV8 (Characterisation).

## Where to add new leaves-flavored theorems

Match by characterisation (parity, mod, depth-vs-leaves).
