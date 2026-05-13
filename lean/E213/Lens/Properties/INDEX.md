# `Lens/Properties/` — Lens predicates + properties

Predicates *about* a Lens (is it a leaf? canonical?  does it have
A-B refinement?  ...) and the theorems characterising them.

## Files (10)

  - `ABRefines.lean` — `ABRefines` predicate
  - `CanonicalForm.lean` — `universalLens_recovers` canonical form
  - `ConstLensTotalKernel.lean` — constant-Lens kernel = `Raw × Raw`
  - `EquivProperties.lean` — equiv-induced facts
  - `InjectiveClass.lean` — injective Lens characterisation
  - `IsLeaf.lean` — leaf predicate
  - `Leaf.lean` — leaf theorems
  - `ParityCollapseFalse.lean` — parity collapse counterexample
  - `ProdBelowId.lean` — product-Lens-below-identity facts
  - `TowerLevel3.lean` — level-3 Lens-tower facts

## Public API

Re-exported via `E213.Lens.API` (HV6/HV8 categories).

## Where to add new property theorems

Match the file by predicate name; if new predicate, create new file.
