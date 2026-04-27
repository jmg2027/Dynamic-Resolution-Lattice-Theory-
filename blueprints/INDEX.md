# 213 Library Blueprints — Master Index

The *map* of the 213 library — future marathons + Kernel meta.

## Track INDEX

  📋 **Meta Track**    `blueprints/meta/`               (kernel philosophy + phases)
  📐 **Math Track**     `blueprints/math/INDEX.md`       (14 fields)
  ⚛️ **Physics Track** `blueprints/physics/INDEX.md`     (14 fields)

## Meta — 213 Kernel (★★★★ Top Priority, KA→KH complete)

  - `meta/01_213_kernel.md`         Vision + building blocks + Phase overview
  - `meta/01_213_kernel_phases.md`  KB→KH detail + open problems

Status: **All 101 theorems verified 0 axiom** (`./tools/kernel_regress.sh`).
None of propext / Quot.sound / Classical.choice in the Lean kernel are
load-bearing — "Lean = syntactic host, 213 = real foundation" is a
formal fact.

## Architecture

  📋 `math/00_DIRECTORY_PROPOSAL.md`  — Math track directory proposal
  📋 `physics/00_PHYSICS_RESPONSE.md` — Physics track response (full agreement)

  Final architecture consensus:
  - `seed/` (axioms + philosophy + falsifiability)
  - `lean/E213/` (namespace preserved)
  - `lean/E213/Math/{Analysis, Probability, ...}` sub-dirs
  - `lean/E213/Physics/{Foundation, Atoms, ...}` sub-dirs
  - `lean/E213/Library/` catalog module
  - `papers/`, `books/{math,physics}/`, `catalogs/`,
    `examples/`, `blueprints/{math,physics}/`, `tools/`
  - **no `archive/`** (CLAUDE.md "delete deprecated")

## Division of Work

  - Math track: lean/E213/Math/, books/math/, math/01-12,14
  - Physics track: lean/E213/Physics/, books/physics/, physics/all
  - Common: seed/, catalogs/, papers/, examples/, tools/

## Progress Priorities (★★★ Top Priority)

### Math
- 01 Probability (FluxCut already done)
- 02 Multivariable
- 03 Topology
- 10 Combinatorics (atomic native)
- 13 213 Meta

### Physics
- 01 Atomic Physics (Phase 4 already done)
- 02 Hadron (m_p 0.000%)
- 03 Nuclear (magic 7/7)
- 04 Cosmology (Ω_Λ 0.0008%)
- 05 Gauge (137 ppm)
- 07 Yang-Mills (Clay)
- 10 Falsifier (CLAUDE.md criterion 2)
- 13 Beyond SM (refutation)

## How to Use

New session:
1. Select a field following the priorities above
2. Read the blueprint carefully (Phase plan + building blocks)
3. Proceed with the marathon
4. Integrate results (Lean + book + catalog)

## Integrated build

```bash
cd lean/
lake build E213
# → Both tracks clean, 0 sorry, ≤ propext + Quot.sound
```
