# 13 — Critical Line & Riemann Hypothesis

**Tier:** T3/T2 hybrid (mostly external; finite incompleteness sharpens)
**Status:** Not yet 4/27 closed; framework in papers, no Lean.
**Lean:** (none yet — this is the largest open math chapter).

## Best current statement

213's number-theoretic content lives in the f_occ spectrum (Ch. 03)
and its connection to ζ(2) via the Basel sum (`BaselBound.lean`). The
critical-line story extends this to ζ(s) for s in the strip.

### Born-rule weighted Gram graphs (paper5)

`paper5_critical_line.tex` formulates ζ(s) zeros in terms of spectra of
Born-rule-weighted Gram matrices over the f_occ spectrum. The
critical line Re(s) = 1/2 emerges as the *equilibrium between forward
and backward flux* on these graphs (connects to FluxCut, Ch. 14).

### Finite Incompleteness of RH (paper7)

`paper7_finite_incompleteness.tex` argues that RH, *as classically
stated over ℂ*, is **not decidable in any finite resolution** because
the critical strip contains a continuum of candidate zeros. 213's
discrete reformulation — RH as a statement about Born-rule Gram
spectra — is decidable in finite resolution.

### Spectral complexity (paper9)

`paper9_spectral_complexity.tex` characterizes the complexity class of
ζ-spectrum verification on the Born-rule Gram graph; connects to
P ≠ NP (paper11) at the meta-level via Abel-Ruffini analog.

## 213 sharpening

- "Is RH true?" → reformulated: "is the f_occ-Gram spectrum on-line?".
  The reformulation is decidable; classical RH is not.
- ζ(2) → S(N) bracket with width tightening; same method extends to
  general ζ(s) but bracketing is unproven.
- Finite incompleteness as a positive structural feature, not a
  negative result.

## Open / next (largest chapter — most work pending)

- **Lean formalization of the Gram graph spectrum** (paper5 → Lean).
  Currently no `lean/E213/` module covers this. First marathon target.
- Finite incompleteness theorem in Lean (paper7 → Lean).
- BSD, Hodge, Poincaré, P ≠ NP papers (10, 11, 12, 13, 16) all sit in
  this T3 layer pending the foundational paper5 → Lean work. They are
  treated separately in the appendix; see `appendix_paper_origins.md`.

## Sources

- `papers/paper5_critical_line.tex` (Born-rule Gram graph)
- `papers/paper7_finite_incompleteness.tex` (RH finite incompleteness)
- `papers/paper9_spectral_complexity.tex` (complexity of ζ-spectrum)
- `papers/paper10_hodge.tex`, `paper11_p_ne_np.tex`, `paper12_bsd.tex`,
  `paper13_poincare.tex`, `paper16_exponent_barrier.tex` —
  Millennium-class applications, all currently external-only.
- `lean/E213/Lib/Physics/BaselBound.lean` (the only ζ-related Lean module).
