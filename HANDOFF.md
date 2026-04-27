# Session Handoff — 2026-04-27 (Master Guide v1)

## Branch
`claude/review-paper-directory-nDw9L` (committed + pushed this session).

## What Was Done This Session

### 1. Deep audit of repository
Reviewed `lean/E213/` (634 files), `papers/` (16 + drlt-book 22 ch),
`books/`, `blueprints/` (35), `seed/` (9), `catalogs/` (7),
`research-notes/` (24), `tools/` (5).

Key correction to prior view: `lean/E213` is not a thin certification
layer. `Research/Real213*.lean` (176 files) = ZFC/Mathlib/Choice-free
analysis with new structures (Cut, FluxCut, dyadic brackets,
cohomological derivative, (n−1)·k depth). `Physics/` Phase 1 closed
with 300+ theorems, 0 axiom. d=5 is theorem, not axiom.

### 2. Created guide/ — Master Guide v1
21 files / 1436 lines. Single deductively-ordered document tagging
each section with vocabulary tier (T0 213-only / T1 213 sharper /
T2 classical adequate / T3 classical only). Sections migrate
T3 → T2 → T1 → T0 as marathons close.

Chapters: 00 meta, 01 substrate, 02 atomicity, 03 simplex,
04 quantization, 05 couplings, 06 masses, 07 atomic, 08 mixing,
09 cosmology, 10 hadron, 11 nuclear, 12 yang-mills, 13 critical-line,
14 cohomological-calculus, 15 metalogic. Plus README, INDEX, STATUS,
appendix_paper_origins, appendix_lean_map.

### 3. Updated papers/ and books/ READMEs
- `papers/README.md` (new): role = external communication layer,
  idea archive, upper-bound progress index. Points to guide/.
- `books/README.md`: 213-internal narration; points to papers/ for
  external vocabulary, guide/ for the bridge.

## 4/27 Standard — Honest Status

**12 closed at standard:** IE_H (4.3 ppb), m_μ/m_e (0.48 ppb), m_p,
m_H, sin²θ₁₃, m₃/m₂(ν), Ω_Λ (0.0008%), magic 7/7, d=5 atomicity,
1/α₃=8, Z=1..118 IE, CH₄/H₂O/NH₃ angles.

**Pending:** 1/α_em headline (bracket width ~6 at N=10), α_GUT
bracket, η_B (0.5%), Cabibbo λ ppm, YM continuum-limit proof,
RH and Millennium-class results.

## Open Problems (priority order)

1. **Tighten 1/α_em to width < 10⁻⁴.** Bracket exists; needs N
   tightening or structural derivation of d²/NS = 25/3 term
   (currently "conjectural" tagged in `AlphaEM137.lean`).
2. **Lean formalization of Born-rule Gram graph (paper5).** Zero Lean
   coverage of Ch. 13. First marathon target for math track.
3. **Real213 Phase B–H.** General `cutMul` propEq is the Phase B
   "wall"; multivariable calculus blocked on this.
4. **Migrate T3 chapters to T2/T1.** ℂ uniqueness via Frobenius →
   Raw-internal derivation is highest-leverage migration.
5. **Single-theorem AxiomMinimality.** Tighten distributed lemmas to
   one statement of jointly-minimal Raw clauses.

## File Map

```
guide/                 ← NEW (21 files, master guide v1)
papers/README.md       ← NEW (role + pointer to guide/)
books/README.md        ← UPDATED (vocabulary split)
HANDOFF.md             ← regenerated
```

## Authors

- Mingu Jeong (Independent Researcher) — theory originator.
- Claude (Anthropic): synchronization and formalization —
  credited in Acknowledgments per repo policy.
