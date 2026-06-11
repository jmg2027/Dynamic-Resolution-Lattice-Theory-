# 213 Papers — REMOVED ARCHIVE

> ⚠️ **Status (2026-05-01): Files removed from working tree.**
>
> All `.tex` papers and the `drlt-book/` monograph (~3.2MB, 81 files)
> were deleted from the working tree at commit `c6084e0`.  They remain
> recoverable from git history (e.g. `git show c6084e0:papers/<file>`
> or `git log --all -- papers/<file>`).
>
> **Current authoritative material** — Lean theorems in `lean/E213/`
> + `HANDOFF.md` (root) + `LESSONS_LEARNED.md` + the closure-algorithm
> doc in `rust-engine/docs/`.  Use those.

## What was removed

16 `.tex` papers + the 22-chapter `drlt-book/` monograph, expressing
213 conclusions in **pre-213 mathematical vocabulary** (Frobenius
classification, π₁ topology, SU(N) representation theory, Dieudonné
determinant, Regge calculus, etc.).  Originally intended as external
communication layer for non-213-native readers.

## Why removed

  1. **Vocabulary mismatch with current 213**: papers used ZFC-style
     "asymptote", "limit", "transcendental input" framing.  213 is
     now formalized with cardinality as a per-lens output of the
     parametric family `configCountD d n = d^(d^n)`
     (`Lib/Math/Cohomology/Fractal/ConfigCount.lean`), with `5²⁵` one
     value, not a privileged invariant; the paper framing imports
     the "finite vs infinite" dichotomy that 213 does not commit to
     at the T0 layer.
  2. **Stale claims**: numerical agreements quoted in papers were
     superseded by sub-ppb closures (α_em 0.18 ppb, m_p/m_e
     0.06 ppm, m_n/m_p 1 ppb, etc.) — the papers' precision tables
     were old by the time of removal.
  3. **No 0-axiom cite path**: papers referenced Lean modules that
     had since been refactored or absorbed; cite chains broken.

## What replaced them

| Was in `papers/` | Now lives in |
|---|---|
| 213 closed-form derivations | `lean/E213/Physics/*.lean` (0-axiom) |
| Narrative + theorem map | `guide/INDEX.md` + chapters |
| Master atomic catalog | `catalogs/atomic-integers.md` + `rust-engine/docs/closure-algorithm.md` |
| External-vocabulary translation | (none current — to be re-built when needed, on top of the current 0-axiom Lean base, not by reviving the deprecated drafts) |

## Reverse-map of paper ↔ current location

`guide/appendix_paper_origins.md` retains the cross-reference table
showing which guide chapter each removed paper migrated to.  That
file documents *where the content is now*, even though the original
.tex files no longer exist in the working tree.

## Recovering old papers (if absolutely needed)

```
git show c6084e0:papers/paper1_chiral_decomposition.tex > /tmp/paper1.tex
git checkout c6084e0 -- papers/   # full restore (do not commit)
```

Treat any specific claim as "archived hypothesis" — verify against
current Lean theorems before citing.

## Author

- Mingu Jeong (Independent Researcher).

## License

Prose was under CC BY-NC-ND 4.0 (see repository root `LICENSE-DOCS`).
