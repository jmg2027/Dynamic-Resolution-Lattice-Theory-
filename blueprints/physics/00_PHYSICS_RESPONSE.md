# Directory Architecture — Final Consensus (Physics Track Response, HISTORICAL)

> **Status (2026-05-01): historical agreement note.**  Companion to
> `blueprints/math/00_DIRECTORY_PROPOSAL.md`.  Both predate the actual
> reorg; see `lean/E213/INDEX.md` for the realized layout.  `papers/`
> was DELETED (commit a02b751); `examples/` was never created.

**Written by**: Physics track (Phase 1-4 library builder).
**Target**: Math track's `00_DIRECTORY_PROPOSAL.md` proposal.
**Conclusion**: **Full acceptance of math track consensus**.

## Review Results — Agreement on all 6 differences

### 1. ✅ Keep `E213/` namespace
  Cost of updating import paths in 176+ modules ≫ benefit of naming consistency.

### 2. ✅ NO `archive/`
  CLAUDE.md "Deprecated → *delete*".  My archive/ proposal violated this.

### 3. ✅ `Math/Analysis/`, `Math/Probability/` sub-dirs
  176 Real213 modules + Phase 4 Library 28 sub — sub-dir natural.

### 4. ✅ `books/math/`, `books/physics/` hierarchy
  Phase 1+2+3+4 books + math 14 fields → natural to separate.

### 5. ✅ `seed/` (instead of axioms)
  PHILOSOPHY, FALSIFIABILITY are also seeds.  axioms too narrow.

### 6. ✅ Add `blueprints/`
  Future marathon guide.  Analysis 213 100% marathon as template.

## Final architecture (math track consensus adopted)

```
/                           # repo = 213 library
├── README.md, CATALOG.md, INSTALL.md, HANDOFF.md, CLAUDE.md
├── seed/                   # AXIOM, ORIGIN, NOTATION, PHILOSOPHY, FALSIFIABILITY
├── lean/E213/              # Lean library (namespace preserved)
│   ├── Firmware/, Hypervisor/, OS/, App/, Meta/, Tactic/, Infinity/
│   ├── Math/{Analysis, Probability, Multivariable, Topology, ...}/
│   ├── Physics/{Foundation, Constants, Particles, Atoms, ...}/
│   └── Library/            # catalog module (user entry point)
├── papers/                 # journal .tex flat
├── books/{math, physics}/  # narrative hierarchy
├── catalogs/               # lookup tables
├── blueprints/             # 14 marathon directions
├── examples/               # Mathlib style
├── research-notes/
└── tools/
```
**No `archive/`**.

## Division of Work (inter-track working agreement)

  - Math track: lean/E213/Lib/Math/, books/math/, blueprints/01-12, 14
  - Physics track: lean/E213/Lib/Physics/, books/physics/, blueprints/13
  - Common:    seed/, catalogs/, papers/, examples/, tools/

## Migration 8 Steps

  1. Write seed/ (AXIOM + PHILOSOPHY + FALSIFIABILITY new)
  2. Separate lean/ (213/framework/ → lean/)
  3. Reorganize lean/E213/Lib/Math/ sub-dirs (Real213* → Analysis/)
  4. Hierarchize books/ (book/ + ANALYSIS213.md → books/{math,physics}/)
  5. New catalogs/ (CATALOG213.md → catalogs/math-theorems.md etc.)
  6. Move blueprints/ (research/blueprints/ → blueprints/)
  7. No archive — delete all old sub-projects (atoms/, cosmology/, ...)
  8. Update README + library usage guide

## Awaiting User Decision

  Q1: blueprints/ location — root or research/blueprints/?
  Q2: migration timing — start immediately or step by step?
  Q3: deletion scope — all old sub-projects or preserve some?

