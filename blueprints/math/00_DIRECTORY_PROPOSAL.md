# Directory Structure Proposal — 213 Library Consensus

**Written by**: Math track (Analysis 213 marathon completer).
**Compared against**: Physics track directory proposal.
**Goal**: Satisfy both tracks + comply with CLAUDE.md organization principles + future extensibility.

---

## 1. Core Consensus Points (both tracks agree)

✅ **`lean/` separation** — Lean code in its own namespace dir
✅ **`Library/` catalog module** — user entry point (IELibrary, etc.)
✅ **`books/` narrative separation** — *readable books* distinct from papers
✅ **`catalogs/` lookup tables** — grep-able
✅ **`examples/` Mathlib style** — improved usability
✅ **`tools/` CLI** — atomic chain search

## 2. Differences + Consensus

### 2.1 Namespace: `DRLT/` vs `E213/`

**Physics**: `DRLT/`
**Math**: keep `E213/`

**Consensus**: keep `E213/`.  Rationale:
- Updating import paths in 80+ Lean commits (large side effect)
- `DRLT` = theory name, `E213` = Lean identifier — keep them separate
- `lean/E213/` form is clear

### 2.2 Old code: `archive/`

**Physics**: preserve `archive/` directory
**Math**: none

**Consensus**: do not create `archive/`.  Rationale:
- CLAUDE.md "Deprecated → *delete*"
- Value of "historical record" = noise
- git history is sufficient

### 2.3 Math code organization

**Physics**: single `Math/Calculus.lean`
**Math**: `Math/Analysis/`, `Math/Probability/` sub-dirs

**Consensus**: adopt sub-dirs.  Rationale:
- Analysis 213 = 176 modules — single file impossible
- 80-line Lean hook
- 14 blueprints planned per field (probability, multivariable, ...)
- Each field gets a sub-dir + `_root.lean` umbrella

### 2.4 books: flat vs hierarchical

**Physics**: 11 chapters flat
**Math**: `books/math/`, `books/physics/` hierarchy

**Consensus**: adopt hierarchy.  Rationale:
- Flat structure becomes confusing as field depth increases
- Analysis 213 alone requires separate `ANALYSIS213.md` (370 lines)
- Many books → natural to split math/ vs physics/

### 2.5 Seed directory

**Physics**: `axioms/` (AXIOM, PAPER1, ORIGIN, NOTATION)
**Math**: `seed/` (above + PHILOSOPHY, FALSIFIABILITY)

**Consensus**: `seed/`.  Rationale:
- "Axioms" alone are not the only seeds — philosophy and falsifiability are too
- Falsifiability from AXIOM.md §5.2.1 is a core seed
- "axioms" is too narrow a framing

### 2.6 Blueprints (math track addition)

**Physics**: none
**Math**: add `blueprints/`

**Consensus**: adopt.  Rationale:
- Direction documents for 14 future marathon fields
- Identifies fields capable of a 100% marathon like Analysis 213
- Guides new sessions on where to start

---

## 3. Final Consensus (Tree, 1/2)

```
/                               # repo = 213 library
├── README.md
├── CATALOG.md                  # ★ master entry
├── INSTALL.md
├── HANDOFF.md
├── CLAUDE.md
├── LICENSE
│
├── seed/                       # ★ seeds
│   ├── AXIOM.md
│   ├── ORIGIN.md
│   ├── NOTATION.md
│   ├── PHILOSOPHY.md
│   └── FALSIFIABILITY.md
│
├── lean/                       # ★ Lean 4 formal library
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── E213/
│       ├── Firmware/
│       ├── Hypervisor/
│       ├── OS/
│       ├── App/
│       ├── Meta/
│       ├── Tactic/
│       ├── Infinity/
│       ├── Math/
│       │   ├── Analysis/       # current Real213*
│       │   ├── Probability/    # blueprint 01
│       │   ├── Multivariable/  # blueprint 02
│       │   ├── Topology/       # blueprint 03
│       │   ├── Complex/        # blueprint 04
│       │   ├── Measure/        # blueprint 05
│       │   ├── ODEPDE/         # blueprint 06
│       │   ├── Number/         # blueprint 07
│       │   ├── Functional/     # blueprint 08
│       │   ├── Linear/         # blueprint 09
│       │   ├── Combinatorics/  # blueprint 10
│       │   ├── Group/          # blueprint 11
│       │   ├── Information/    # blueprint 12
│       │   ├── Logic/          # blueprint 14
│       │   └── _root.lean
│       ├── Physics/
│       │   ├── Foundation/
│       │   ├── Constants/
│       │   ├── Particles/
│       │   ├── Atoms/
│       │   ├── Nuclear/
│       │   ├── Hadron/
│       │   ├── Cosmology/
│       │   ├── YangMills/
│       │   └── _root.lean
│       └── Library/            # ★ catalog module
│           ├── IELibrary.lean
│           ├── CouplingLibrary.lean
│           └── ... (28+)
```

## Tree (2/2)

```
├── papers/                     # journal .tex flat
│   ├── analysis213.tex
│   ├── physics213.tex
│   └── architecture213.tex
│
├── books/                      # ★ narrative hierarchy
│   ├── README.md
│   ├── 00-overview.md
│   ├── math/
│   │   ├── analysis213.md
│   │   ├── probability213.md
│   │   └── ...
│   └── physics/
│       ├── periodic-table.md
│       ├── particle.md
│       └── ...
│
├── catalogs/                   # ★ lookup tables
│   ├── README.md
│   ├── atomic-integers.md
│   ├── physics-constants.md
│   ├── periodic-table.md
│   ├── correspondences.md
│   ├── falsifiers.md
│   ├── lemma-index.md
│   ├── math-theorems.md        # ★ math track addition
│   └── modules.md              # ★ Lean module → theorem mapping
│
├── blueprints/                 # ★ future marathon directions
│   ├── INDEX.md
│   ├── 00_DIRECTORY_PROPOSAL.md  (this file)
│   ├── 01_probability_213.md
│   ├── 02_multivariable_213.md
│   └── ... (14 fields)
│
├── examples/                   # Mathlib style
│   ├── README.md
│   ├── 01-hello-atomic.lean
│   ├── 02-compute-ie.lean
│   ├── 03-verify-prediction.lean
│   ├── 04-atomic-chain.lean
│   ├── 05-import-other-project.lean
│   ├── math-01-mvt.lean        # ★ math examples
│   ├── math-02-integral.lean
│   └── math-03-transcendental.lean
│
├── research-notes/             # research notes (current 213/research/notes/)
│   ├── 17_existence_mode_lens.md
│   ├── 19_lens_not_functor.md
│   └── ...
│
└── tools/                      # CLI
    ├── lookup_integer.py
    ├── search_constant.py
    └── catalog_grep.sh
```

---

## 4. Migration Steps

Major steps from current → consensus (work for next session):

### Step 1: seed/ directory

`213/AXIOM.md`, `ORIGIN.md`, `NOTATION.md` → `seed/`.
Write new PHILOSOPHY.md, FALSIFIABILITY.md.

### Step 2: lean/ separation

`213/framework/` → `lean/`.  Move Lakefile + lean-toolchain.
Keep `E213/` namespace as-is.

### Step 3: lean/E213/Math/ per-field sub-dirs

Current `Real213*.lean` 176 modules → `Math/Analysis/Real213*.lean`.
Keep filenames (renaming would require updating import paths).

### Step 4: books/ hierarchy

Flat `book/` → `books/math/`, `books/physics/`.
`ANALYSIS213.md` → `books/math/analysis213.md`.

### Step 5: new catalogs/

`CATALOG213.md` → `catalogs/math-theorems.md` (or split as master).

### Step 6: blueprints/ unchanged (already written)

`213/research/blueprints/` → keep as-is or move to root.

### Step 7: do not create archive/

Old Python experiments in current sub-projects: migrate *results only*
into 213; delete the old Python itself (**deletion**, git history preserved).

---

## 5. Core Principles

| Principle | Source |
|---|---|
| Deprecated → delete | CLAUDE.md |
| 80-line hook | enforced |
| Natural reading order | CLAUDE.md |
| Adding external axiom = theory discarded | AXIOM.md §5.2.1 |
| 0 sorry, axioms ≤ {propext, Quot.sound} | formal verification standard |
| Mathlib-free | Lean 4 core only |

These 6 principles are *maintained* even through directory changes.

---

## 6. Conclusion

**70% consensus** (Library module, examples, tools, catalogs, books separation).
**30% difference** (namespace, archive, math sub-dir, books hierarchy, seed naming).

From the math track's perspective, the consensus is more equitable for both
sides and increases future extensibility.

Awaiting physics track review + user decision.

