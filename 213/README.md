# 213

**The minimal system of binary relations.**

A formal investigation of what structure follows from the single
3-clause axiom:

> 1. *Something exists.*
> 2. *To know what it is, another something is required.*
> 3. *That other something is also a something.*

Clauses (1) + (3) give at least two somethings; clause (2) is the
primitive *distinction* operation, applied recursively. The
framework is split into **firmware** (the Raw type, §1) and
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
├── E213.lean                           -- library entry (layered imports)
├── E213/
│   ├── Firmware/                       -- layer 1: raw primitive
│   │   └── Raw.lean                    -- Raw API (Tree internal/private),
│   │                                      Raw.a/b, smart slash + slash_comm,
│   │                                      Raw.fold catamorphism
│   ├── Hypervisor/                     -- layer 2: lens (uses Firmware API)
│   │   └── Lens.lean                   -- Lens + view + equiv + refines
│   ├── OS/                             -- layer 3: algorithms / theorems
│   │   ├── Pigeonhole.lean             -- Fin injection bound
│   │   ├── ArityForcing.lean           -- (N=2, k=3) vacuous
│   │   ├── ArityForcingGeneral.lean    -- (N < k) vacuous
│   │   ├── NonDecomposable.lean        -- {2, 3} characterization
│   │   ├── PrimitiveSizes.lean         -- {2, 3} from axiom
│   │   ├── Alive.lean                  -- antisymmetric-multiplicity postulate
│   │   ├── Atomicity.lean              -- n = 5 via Bézout
│   │   └── PairForcing.lean            -- (p,q)=(2,3) uniqueness
│   └── App/                            -- layer 4: applications
│       └── Simplex.lean                -- (3,2) partition, block invariance
├── lakefile.toml
├── lean-toolchain                      -- leanprover/lean4:v4.16.0
└── lake-manifest.json
```

**Layering rule.** Each layer imports only the public API of layers
below it. In particular:

- `Firmware` hides the internal `Tree` representation
  (`private inductive`); consumers see `Raw` + its smart
  constructors + `Raw.fold` catamorphism.
- `Hypervisor` implements `Lens.view` via `Raw.fold` — no Tree
  access.
- `OS` and `App` build on Hypervisor / earlier OS modules.

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
