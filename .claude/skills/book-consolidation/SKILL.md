---
name: book-consolidation
description: Consolidate all correct theory into the book. Triggered by "book 정리", "book 통합", "consolidate book", "모든 이론을 book에". Ensures the book is the single source of truth, all chapters are synced, and the repo is clean.
---

# Book Consolidation Skill

Ensure `book/` contains ALL correct theory from the entire repo.
The book is the **single source of truth** — after consolidation,
reading only the book should give a complete, consistent picture.

## Phase 1: Survey (read-only)

1. **Scan for unintegrated content:**
   ```
   - research-notes/**/*.md  — new results not yet in book?
   - papers/*.tex            — content diverged from book chapters?
   - experiments/EXP_*.py    — results not referenced in book?
   - results/EXP_*.txt       — key findings not in appendix_verification?
   - Root *.tex, *.md, *.pdf — stray files needing placement?
   ```

2. **Check other branches** for new content:
   ```bash
   git fetch origin
   git branch -a  # look for session-handoff, feature branches
   git log origin/<branch> --oneline -20  # check for new commits
   ```

3. **Diff book vs research-notes** — identify any theorem, formula,
   or precision result in notes that isn't in the corresponding chapter.

## Phase 2: Integrate into Book

### New standalone papers → chapters
For each `.tex` paper not yet in `book/chapters/`:
1. Strip preamble (`\documentclass` through `\begin{document}`)
2. Strip `\maketitle`, `\title`, `\author`, `\date`, `\end{document}`
3. Strip `\begin{abstract}...\end{abstract}` (fold into intro paragraph)
4. Strip `\begin{thebibliography}...\end{thebibliography}`
5. Demote headings: `\section` → `\subsection` → `\subsubsection`
6. Add: `\section{Title}\label{ch:label}` + intro paragraph
7. Apply book macros: `\CC`, `\RR`, `\CP`, `\agut`, `\nS`, `\nT`, `\tr`, `\rank`
8. Write to `book/chapters/ch{NN}_{name}.tex`
9. Add `\input{chapters/ch{NN}_{name}}` to `book/main.tex`
10. Move original to `papers/` (standalone submission copy)

### New theory from research-notes → existing chapters
For validated results not yet in the book:
1. Identify target chapter (see chapter map below)
2. Edit chapter with small, incremental changes
3. Ensure all formulas use book notation and conventions
4. Cross-reference other chapters where appropriate

### New experiments → appendix_verification.tex
Add key results from new experiments to the verification compendium.

## Phase 3: Sync & Clean

1. **Regenerate `drlt_book_single.tex`:**
   ```bash
   cd book && python3 -c "
   import re
   with open('main.tex') as f: main = f.read()
   # ... concatenation script (see existing code in repo)
   "
   ```

2. **Organize non-book files:**
   | File type | Destination |
   |-----------|-------------|
   | Standalone .tex papers | `papers/` |
   | Research .md notes | `research-notes/` or `research-notes/simplex-geometry/` |
   | Axiom derivations | `research-notes/axiom/` |
   | Workflow/review docs | `research-notes/` |
   | Stray root files | Move to appropriate directory |

3. **Update documentation:**
   - `CLAUDE.md`: experiment catalog, open problems, precision table
   - `README.md`: repo structure, key results table

4. **Commit and push** with descriptive message.

## Chapter Map (content → chapter)

| Content domain | Chapter file |
|---------------|-------------|
| Why C, Frobenius, division algebras | `ch01_whyC.tex` |
| Why d=5, atomic dimensions, swap | `ch02_whyd5.tex` |
| (2,3) uniqueness for any N | `ch02c_rep_uniqueness.tex` |
| Simplex combinatorics, hinge types | `ch02b_simplex_geometry.tex` |
| Three theorems (δ=π, det=2/3, c=2) | `ch02d_variational_theorems.tex` |
| Gram matrix, metric, gauge, shadow | `ch03_geometry.tex` |
| Planck constant, Holevo, ZPE | `ch04_hbar.tex` |
| Coupling constants, Binet-Cauchy | `ch05_couplings.tex` |
| Fermion masses, closed propagator | `ch06_masses.tex` |
| Atoms, molecules, bond angles | `ch06b_atoms.tex` |
| CKM, PMNS, CP, Higgs, neutrinos | `ch07_mixing.tex` |
| Trace conservation, ghost sum | `ch08_ghosts.tex` |
| Cosmology, baryon asymmetry, Ω_Λ | `ch09_cosmology.tex` |
| Block universe, rank cascade | `ch10_block.tex` |
| Yang-Mills mass gap | `ch11_yang_mills.tex` |
| Compact stars, neutron/quark stars | `ch12_compact_stars.tex` |
| Webb dipole, α variation | `ch13_webb_dipole.tex` |
| Path integral on CP⁴ | `appendix_path_integral.tex` |
| Numerical verification | `appendix_verification.tex` |
| QCD phenomenology | `appendix_qcd.tex` |
| Core algorithms | `appendix_code.tex` |
| Hydrogen precision | `appendix_hydrogen.tex` |

## Invariants (must be true after consolidation)

- [ ] Every proven theorem in research-notes is in the book
- [ ] Every precision result in CLAUDE.md table is in the book
- [ ] `drlt_book_single.tex` matches the multi-file book exactly
- [ ] No `.tex` or `.md` theory files remain in repo root
- [ ] `papers/` contains only self-contained submission copies
- [ ] `research-notes/` contains only historical working documents
- [ ] CLAUDE.md experiment catalog is up to date
- [ ] CLAUDE.md open problems reflect current state
