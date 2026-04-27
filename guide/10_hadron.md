# 10 — Hadron Spectrum

**Tier:** T2
**Status:** Several closed at sub-percent; full spectrum not yet a
single Lean theorem.
**Lean:** `Physics/HadronMasses.lean`, `Physics/ColorConfinement.lean`,
`Physics/QCD.lean` (selected).

## Best current statement

Hadron masses follow from the GMOR-like relation built on the chiral
atomic decomposition (Ch. 02), with f_occ spectrum entries supplying
the rational coefficients.

### 4/27-passing closures

| Hadron | DRLT | Observed | Error |
|--------|------|----------|-------|
| m_π (pion) | 137.6 MeV | 137.3 MeV | +0.2% |
| m_ω (omega) | 782.1 MeV | 782.7 MeV | −0.07% |
| m_J/ψ | 3081.6 MeV | 3096.9 MeV | −0.5% |
| Δ-N split | 295.7 MeV | 294 MeV | +0.6% |

Each closed `by decide` against observed values.

### Color confinement (closed)

`ColorConfinement.lean` derives 1/α₃ = NS² − 1 = 8 (Discovery 2;
photon = cycle space of K_{3,2}). This is the *confined* coupling.
Asymptotic freedom is `Physics/AsymptoticFreedom.lean` — α₃(Q) running
matched to 5-loop QCD at the percent level.

### Hyperfine and decay constants

Narrative-only in `paper3` and `drlt-book ch19`. Formalization pending.

## 213 sharpening

- "Why m_π appears at ~140 MeV" → answer: GMOR scale × atomic factor;
  no quark condensate parameter.
- "Why color confinement" → answer: the topological identification
  α₃ = 1/8 at d = 5 with cycle structure of K_{3,2}. Replaces the
  asymptotic-freedom-only story of QCD.
- Δ-N splitting follows from the same chiral atomic decomposition that
  produces the lepton masses in Ch. 06 — single source.

## Open / next

- Full meson + baryon octet/decuplet in one Lean module.
- Hyperfine splittings (currently narrative).
- Tighten m_π from +0.2% to ppm closure.
- Connect to YM mass gap (Ch. 12) — both should reduce to the same
  underlying lattice spectrum.

## Sources

- `papers/paper3_zero_parameter_predictions.tex` (hadron table)
- `papers/drlt-book/chapters/ch19_qcd.tex`
- `lean/E213/Physics/HadronMasses.lean`, `ColorConfinement.lean`,
  `AsymptoticFreedom.lean`, `QCD.lean`.
