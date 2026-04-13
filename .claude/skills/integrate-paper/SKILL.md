---
name: integrate-paper
description: Move PDF/TeX papers from root to book/ and integrate key results into the appropriate book chapter. Triggered by "논문 올렸어", "이것도 올렸어", "PDF 올렸어", "paper uploaded", etc.
---

# Paper Integration Skill

When a new PDF/TeX paper appears in the repo root, move it to
`papers/` and integrate its key results into the book.

## Workflow

### 1. Detect new files
```bash
ls *.pdf *.tex 2>/dev/null  # check root for new papers
```

### 2. Move to papers/
- `"file name.pdf"` → `papers/file_name.pdf`
- `"file name.tex"` → `papers/file_name.tex`
- Replace spaces with underscores

### 3. Analyze content
Read the paper and identify:
- New predictions (formula, observed value, error)
- New theorems/proofs
- Connection points to existing chapters

### 4. Integrate into book

| Content type | Target chapter |
|-------------|---------------|
| Why ℂ, topology, phases | `ch01_whyC.tex` |
| d=5, atomic dimensions | `ch02_whyd5.tex` |
| (2,3) uniqueness | `ch02c_rep_uniqueness.tex` |
| Simplex geometry | `ch02b_simplex_geometry.tex` |
| Variational theorems | `ch02d_variational_theorems.tex` |
| Gram matrix, metric, gauge | `ch03_geometry.tex` |
| ħ, Holevo, ZPE | `ch04_hbar.tex` |
| Coupling constants | `ch05_couplings.tex` |
| Fermion masses, propagator | `ch06_masses.tex` |
| Atoms, molecules, angles | `ch06b_atoms.tex` |
| Mixing, CP, neutrinos | `ch07_mixing.tex` |
| Trace conservation | `ch08_ghosts.tex` |
| Cosmology, Ω_Λ, η_B | `ch09_cosmology.tex` |
| Block universe | `ch10_block.tex` |
| Yang-Mills mass gap | `ch11_yang_mills.tex` |
| Compact stars | `ch12_compact_stars.tex` |
| Webb dipole, α variation | `ch13_webb_dipole.tex` |

### 5. Edit rules
- **Small chunks only** — use Edit tool, never full rewrite
- **G-based axiom** (not W-based, not d=4 input)
- **Add, don't delete** existing content
- Use book macros: `\CC`, `\RR`, `\CP`, `\agut`, `\nS`, `\nT`
- Add cross-references (`\ref`, `\cite`) where appropriate

### 6. Post-integration
```bash
# Regenerate single-file version
cd book && python3 generate_single.py
# Commit
git add papers/ book/chapters/*.tex book/drlt_book_single.tex
git commit -m "Integrate paper: <title>"
git push -u origin <branch>
```

### 7. Update CLAUDE.md if needed
- New experiment → update catalog
- New precision result → update table
