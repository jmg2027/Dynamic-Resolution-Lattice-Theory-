# `Lib/Math/Analysis/Modulus/` — modulus combinators for cut-level analysis

Modulus tracking on Real213 cuts: `HasModulus`, strong/diagonal
moduli, and bounding lemmas.  Used by Cauchy-sequence and
differentiation machinery.

## Files (10)

### Core predicate
  - `HasModulus.lean`             — base `HasModulus` predicate
  - `HasModulusBoundsExtra.lean`  — extra bound lemmas
  - `StrongModulus.lean`          — strong-modulus variant

### Diagonal / depth / info
  - `DiagonalHasModulus.lean`     — diagonal-modulus witness
  - `DiagonalIrrelevance.lean`    — diagonal-irrelevance lemma
  - `DepthCompleteness.lean`      — depth-modulus completeness
  - `InfoClosure.lean`            — information-closure of modulus

### Concrete witnesses + translation
  - `PellHasModulus.lean`         — Pell-seq HasModulus instance
  - `Translation.lean`            — modulus-translation lemma

### Capstone
  - `Capstone.lean`              — modulus capstone

## Where to add new files

  - New HasModulus instance  → `<Seq>HasModulus.lean`
  - Bounding lemma           → `HasModulusBounds*`
  - Diagonal / completeness  → `Diagonal*` / `Depth*`
  - Capstone                 → `Capstone`
