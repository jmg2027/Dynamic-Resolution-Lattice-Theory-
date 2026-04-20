# 213

**The minimal system of binary relations.**

A formal investigation of what structure follows from the single
3-clause axiom:

> 1. *Something exists.*
> 2. *To know what it is, another something is required.*
> 3. *That other something is also a something.*

Clauses (1) + (3) give at least two somethings; clause (2) is the
primitive *distinction* operation, applied recursively. The
framework is split into **firmware** (the raw type, §1) and
**hypervisor** (the Lens layer, §4+), with equality/inequality
arising only at the hypervisor level.

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
│   ├── Clean213.lean               -- Tree, canonical form, Raw subtype,
│   │                                    smart slash + symmetry, Lens
│   ├── Homogeneity.lean            -- swap with re-canonicalization,
│   │                                    Aut(Raw) ≅ ℤ/2
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

No Mathlib dependency; core Lean 4 only. The firmware
(`Clean213.lean`) emulates a **free commutative magma on 2
generators with no fixed points** via a canonical-form subtype
of a free ordered magma. The ordering is an implementation
artifact needed because core Lean lacks primitive quotients; no
set theory (`Multiset`, ZFC-style sets) is imported.

Level-by-level closure:
- Level 0: `{a, b}` — 2 terms
- Level 1: `+ a/b` — 3 terms
- Level 2: `+ a/(a/b), b/(a/b)` — 5 terms, (3, 2) partition

## Scope

The paper covers the minimal formal system induced by the axiom.
It does not address physical or cosmological interpretations.

---

*0 sorry. 0 external axioms beyond the one stated.*
