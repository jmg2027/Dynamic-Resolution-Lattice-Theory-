# 213

**The minimal system of binary relations.**

A formal investigation of what structure follows from the single axiom:

> *There exists a relation object between two objects.*

## Contents

### `PAPER.md`
The formal paper. Theorem–proof style, section-by-section derivation
from axiom to forced codomain (`ℂ`), with explicit dependency
tracking between claims.

### `framework/`
A Lean 4 project verifying the paper's core theorems. `0 sorry`,
built with `lake build`.

```
framework/
├── E213.lean                       -- library entry
├── E213/
│   ├── Clean213.lean               -- Raw, Reachable, Lens, basics
│   ├── Homogeneity.lean            -- swap automorphism, Aut(Raw) ≅ ℤ/2
│   ├── ArityForcing.lean           -- (N=2, k=3) vacuous
│   ├── Pigeonhole.lean             -- Fin k → Fin N injection bound
│   ├── ArityForcingGeneral.lean    -- (N < k) vacuous, arbitrary N, k
│   ├── Atomicity.lean              -- n = 5 uniquely atomic
│   ├── NonDecomposable.lean        -- {2, 3} as non-decomposable ≥ 2
│   ├── PrimitiveSizes.lean         -- {2, 3} read off the axiom
│   ├── AliveFromDistinctness.lean  -- alive as antisymmetric-multiplicity postulate
│   ├── PairForcing.lean            -- (p,q)=(2,3) uniquely forces n=5
│   └── Simplex.lean                -- (3,2) partition, block invariance
├── lakefile.toml
├── lean-toolchain                  -- leanprover/lean4:v4.16.0
└── lake-manifest.json
```

## Build

```
cd framework
lake build
```

No Mathlib dependency; core Lean 4 only.

## Scope

The paper covers the minimal formal system induced by the axiom.
It does not address physical or cosmological interpretations.

---

*0 sorry. 0 external axioms beyond the one stated.*
