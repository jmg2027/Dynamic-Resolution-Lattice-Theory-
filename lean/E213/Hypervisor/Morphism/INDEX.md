# `Hypervisor/Lens/Morphism/` — Lens morphism theory

Technical investigations into Lens morphisms: when one Lens is a
hom-image of another, fold-structured morphisms, distance metrics
on the Lens space, etc.  Mostly internal infrastructure.

## Files (7)

  - `BoolProp.lean` — Bool-valued morphism propositions
  - `BoolSqClassification.lean` — Bool-square classification
  - `Dist.lean` — distance metric on Lens space
  - `DepthParityNotFold.lean` — counterexample: depth-parity is
    not a fold-structured morphism
  - `FoldStructured.lean` — characterisation of fold-structured
    morphisms
  - `NoDepthParity.lean` — companion to DepthParityNotFold
  - (others)

## Public API

Mostly internal.  Selected morphism characterisations available
via `E213.Hypervisor.API` (HV5/HV6 categories).

## Where to add new morphism theorems

Match by morphism category (Bool, fold, distance, ...).
