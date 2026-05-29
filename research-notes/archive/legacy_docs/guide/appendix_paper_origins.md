# Appendix A — Paper Origins (Reverse Map)

For each paper / drlt-book chapter, the chapter(s) of this guide where
its content is now treated, plus migration notes.

## Papers (paper1 — paper16)

| Paper | Title (short) | Guide chapter(s) | Tier here |
|-------|--------------|------------------|-----------|
| paper1 | Chiral atomic decomposition | Ch. 02, Ch. 06 | T0/T2 |
| paper2 | Frobenius → Gauge | Ch. 01, Ch. 05 | T3/T2 |
| paper3 | Zero-parameter predictions | Ch. 06–11 (catalog) | T2 |
| paper4 | ζ-β coupling running | Ch. 04, Ch. 05 | T1/T2 |
| paper5 | Born-rule Gram, critical line | Ch. 13 | T3 |
| paper6 | Simplex coupling | Ch. 03, Ch. 05 | T1/T2 |
| paper7 | Finite incompleteness of RH | Ch. 13 | T3/T2 |
| paper8 | Yang–Mills mass gap (Lean) | Ch. 12 | T1/T3 |
| paper9 | Spectral complexity | Ch. 13 | T3 |
| paper10 | Hodge conjecture on ∂Δ⁴ | Ch. 13 (open) | T3 |
| paper11 | P ≠ NP as Abel-Ruffini | Ch. 13 (open) | T3 |
| paper12 | BSD conjecture | Ch. 13 (open) | T3 |
| paper13 | Poincaré conjecture | Ch. 13 (open) | T3 |
| paper14 | 213 self-describing | Ch. 00 | T0 |
| paper15 | Navier-Stokes (Gram) | Ch. 13 (related) | T3 |
| paper16 | Exponent barrier framework | Ch. 13 (related) | T3 |

## drlt-book chapters (ch01 — ch22)

| Chapter | Title (short) | Guide chapter(s) |
|---------|--------------|------------------|
| ch01 | Why ℂ | Ch. 01 |
| ch02 | Why d = 5 | Ch. 02 |
| ch03 | Representation uniqueness | Ch. 02 |
| ch04 | Simplex geometry | Ch. 03 |
| ch05 | Variational theorems | Ch. 03 (deprioritized — see CLAUDE.md "Algebraic Priority") |
| ch06 | Geometry | Ch. 03 |
| ch07 | ℏ | Ch. 04 |
| ch08 | Couplings | Ch. 05 |
| ch09 | Masses | Ch. 06 |
| ch10 | Atoms | Ch. 07 |
| ch11 | Mixing | Ch. 08 |
| ch12 | Ghosts | (drlt-book only — no current Lean) |
| ch13 | Cosmology | Ch. 09 |
| ch14 | Block | (drlt-book only — narrative meta-chapter) |
| ch15 | Yang–Mills | Ch. 12 |
| ch16 | Compact stars | Ch. 11 (extension) |
| ch17 | Webb dipole | Ch. 09 |
| ch18 | Path integral | Ch. 03 + Ch. 14 |
| ch19 | QCD | Ch. 10 |
| ch20 | Hydrogen | Ch. 04 + Ch. 07 |
| ch21 | Occupation fraction | Ch. 03 |
| ch22 | 213 | Ch. 00 |

## Migration notes

- **paper14 ↔ Ch. 00**: closest paper-Lean pairing in the corpus
  (`Kernel/Sound`, `Term`, `Pair` mirror paper14's swap symmetry).
- **paper3 → catalog form**: best treated as a *reference table* of
  observables. Phase 1 / Phase 4 Lean modules close ~5–6 of 17.
- **paper8 ↔ Ch. 12**: mass gap statement is paper-Lean paired;
  full Clay-Millennium proof of continuum equivalence open.
- **paper5/7/9/10/11/12/13/15/16 → Ch. 13**: all currently
  external-only. Gram-graph Lean formalization is the bottleneck.
- **drlt-book ch05, ch12, ch14**: deprioritized. ch05 (variational)
  contradicts CLAUDE.md "Algebraic Priority"; ch12, ch14 are
  narrative meta-chapters without obvious Lean correspondence.
