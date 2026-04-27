---
name: verify-consistency
description: Deep self-consistency audit of the entire repo. Checks theory, notation, numbers, cross-references, file organization, and documentation. Fixes all inconsistencies found. Triggered by "검증" / "verify", "일관성" / "consistency", "consistency check", "verify", "clean", "정리 검증" / "theorem verify", "audit".
---

# Self-Consistency Verification & Correction

Rigorous audit of the entire repository. Every claim must be
internally consistent. Every number must match everywhere it appears.
Every file must be in the right place. Fix everything found.

## Severity Levels

| Level | Meaning | Action |
|-------|---------|--------|
| **CRITICAL** | Wrong physics, wrong number, contradicts axiom | Fix immediately |
| **ERROR** | Inconsistency between files, broken reference | Fix in this pass |
| **WARNING** | Style inconsistency, suboptimal organization | Fix if easy |
| **INFO** | Minor suggestion, future improvement | Log only |

---

## Phase 1: Axiom & Convention Consistency

Check every `.tex` chapter for violations of core conventions:

### 1.1 The Axiom
- [ ] G_ij = ⟨ψ_i|ψ_j⟩ is fundamental. W = |G|²/d is derived.
- [ ] No chapter treats W as fundamental or axiom.
- [ ] d=5 is derived (Frobenius → ℂ, atomic → d=5), NOT input.
- [ ] Simplices are emergent from high-W cliques, NOT postulated.
- [ ] 1 hinge = 1 bit is derived (Holevo), NOT postulated.

### 1.2 Vertex Labels
The book uses TWO naming conventions. They must NOT be mixed within
a single chapter:
- **A/B convention:** A = spatial (ℂ³), B = temporal (ℂ²)
- **S/T convention:** S = spatial, T = temporal
- `n_S = n_A = 3`, `n_T = n_B = 2` — if both appear, state equivalence.

### 1.3 Key Constants
Every occurrence must use the SAME value:
```
α_GUT = 6/(25π²) = 0.024317...   (use \agut macro)
d = 5
n_S = n_A = 3
n_T = n_B = 2
c = 2 = n_T                       (lattice speed of light)
ε = α^{2/3}(1+α) = 0.08597...    (confinement parameter; book rounds to 0.0860)
φ = golden ratio = (1+√5)/2 = 1.618...
```

### 1.4 Macro Usage
Grep all chapters for raw forms that should use macros:
```bash
grep -rn '\\mathbb{C}' book/chapters/   # should be \CC
grep -rn '\\mathbb{R}' book/chapters/   # should be \RR
grep -rn '\\mathbb{C}P' book/chapters/  # should be \CP
grep -rn 'alpha_.*GUT' book/chapters/   # should be \agut
grep -rn 'operatorname{Tr}' book/chapters/  # should be \tr
grep -rn 'operatorname{rank}' book/chapters/ # should be \rank
```

---

## Phase 2: Numerical Consistency

### 2.1 Cross-file Number Matching
Every precision result appears in multiple locations. ALL must match:
```
Sources to cross-check:
  book/chapters/*.tex     (primary — the standard)
  book/drlt_book_single.tex
  CLAUDE.md               (precision table)
  README.md               (key results table)
  papers/*.tex            (standalone copies)
  results/EXP_*.txt       (experimental outputs)
```

Key values to verify (grep each):
```
137.064    (1/α_em)
938.27     (m_p in MeV)
206.80     (m_μ/m_e)
16.816     (m_τ/m_μ)
6.10e-10   (η_B)
0.6850     (Ω_Λ)
104.52     (H₂O angle)
68.75      (δ_CKM)
0.022      (sin²θ₁₃)
245.6      (v_H in GeV)
```

### 2.2 Formula Verification
For each boxed formula in the book, verify:
- Input values are consistent with stated constants
- Arithmetic produces the claimed output
- Error percentage matches (DRLT value vs observed)

### 2.3 Mass Table Consistency
The complete mass table in ch06_masses.tex must match:
- Individual mass derivations in the same chapter
- Values cited in other chapters (ch07_mixing, ch08_ghosts, etc.)
- CLAUDE.md precision table
- README.md results table

---

## Phase 3: Structural Integrity

### 3.1 LaTeX Compilation Readiness
```bash
# Check for unmatched environments
grep -c '\\begin{' book/chapters/*.tex
grep -c '\\end{' book/chapters/*.tex
# Counts should match per file

# Check for undefined labels
grep -rn '\\label{' book/chapters/ | sed 's/.*\\label{//' | sed 's/}.*//' | sort > /tmp/labels.txt
grep -rn '\\ref{' book/chapters/ | sed 's/.*\\ref{//' | sed 's/}.*//' | sort > /tmp/refs.txt
comm -13 /tmp/labels.txt /tmp/refs.txt  # refs without labels
```

### 3.2 main.tex ↔ chapters/ Sync
- [ ] Every file in `book/chapters/` is `\input{}` in `main.tex`
- [ ] Every `\input{}` in `main.tex` has a corresponding file
- [ ] Part/chapter ordering is logical (Foundation → Simplex → Forces → Matter → Completeness → Applications)

### 3.3 drlt_book_single.tex Sync
- [ ] Contains ALL chapters from main.tex in correct order
- [ ] Preamble matches main.tex exactly
- [ ] Bibliography matches main.tex exactly
- [ ] No stale content from old chapters

### 3.4 File Organization
```bash
# Theory files must not be in root
ls *.tex *.md 2>/dev/null | grep -v CLAUDE | grep -v README | grep -v .gitignore
# Should return nothing (except CLAUDE.md, README.md)

# papers/ must contain only standalone .tex
ls papers/ | grep -v '.tex$'
# Should return nothing

# research-notes/ must not contain .tex book chapters
ls research-notes/*.tex 2>/dev/null
# Should return nothing
```

---

## Phase 4: Documentation Accuracy

### 4.1 CLAUDE.md
- [ ] Experiment catalog matches actual `experiments/EXP_*.py` files
- [ ] "Next: EXP_NNN" matches the actual next available number
- [ ] Resolved problems are genuinely resolved (check referenced EXP)
- [ ] Open problems are still open (not resolved in latest commits)
- [ ] Precision table values match book
- [ ] Repo structure section matches actual directory layout
- [ ] API section matches actual `lib/drlt.py` public methods

### 4.2 README.md
- [ ] Key results table matches CLAUDE.md and book
- [ ] Repo structure matches actual layout
- [ ] Run instructions work (`cd experiments && python EXP_001_pipeline.py`)
- [ ] Book structure table matches actual main.tex

### 4.3 Author Attribution
```bash
grep -rn 'Mingoo\|Min-goo\|Jeong, M\b' book/ papers/
# Should return nothing. Author is always "Mingu Jeong"

grep -l 'Joint research' book/chapters/*.tex papers/*.tex
# Every .tex should have this attribution
```

---

## Phase 5: Theoretical Completeness

### 5.1 Research Notes → Book Coverage
For each file in `research-notes/simplex-geometry/`:
- Is the key result in the book? (theorems, formulas, predictions)
- If superseded, is the book version correct?
- If not yet integrated, flag for integration.

### 5.2 Experiment Results → Book Coverage
For each `results/EXP_*.txt`:
- Are key numerical results referenced in the book?
- Are they in `appendix_verification.tex`?

### 5.3 Three Readings Completeness
From 18_three_readings.md, verify the book covers all three:
1. **det(G_h) reading:** masses, IE, couplings (ch06, ch06b, ch05)
2. **Channel count reading:** PMNS mixing (ch07)
3. **Deficit angle reading:** confinement, Λ (ch11, ch05)

---

## Phase 6: Fix & Report

### Fix Protocol
1. Fix CRITICAL and ERROR items immediately
2. For each fix, use Edit tool (small, incremental changes)
3. After all fixes:
   - Regenerate `drlt_book_single.tex`
   - Run `git diff` to review all changes
   - Commit with message: `"Consistency audit: N fixes (K critical, M error)"`

### Report Format
After all phases, produce a summary:
```
## Consistency Audit Report

### Statistics
- Files scanned: N
- Checks performed: M
- CRITICAL: X (all fixed)
- ERROR: Y (all fixed)
- WARNING: Z (W fixed, V deferred)
- INFO: I

### Fixes Applied
1. [CRITICAL] ch06_masses.tex:142 — m_p value 937.5→938.27
2. [ERROR] README.md — Ω_Λ 0.682→0.6850 to match book
3. ...

### Remaining Items
1. [WARNING] papers/water_angle.tex — old value, update on submission
2. ...
```

---

## Quick Mode vs Full Mode

**Quick mode** (default for "검증" / "verify", "verify"):
- Phase 2.1 (number matching) + Phase 3.3 (single.tex sync) + Phase 4.1 (CLAUDE.md)
- ~5 minutes

**Full mode** ("전체 검증" / "full verify", "full audit", "deep verify"):
- All 6 phases
- ~20 minutes
- Use Agent tool for parallel scanning
