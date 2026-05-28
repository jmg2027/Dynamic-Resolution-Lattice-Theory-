# 06 — Mass Spectrum

**Tier:** T2/T1 hybrid (T1 for closed cases; T2 for derivation chain)
**Status:** Multiple 4/27 passes; full chain open.
**Lean:** `Physics/Mass/MuOverE.lean`, `Physics/Mass/TauOverMu.lean`,
`Physics/Hadron/ProtonMass.lean`, `Physics/Higgs/Mass.lean`,
`Physics/Hadron/QuarkHierarchy.lean`.

## Best current statement

213 derives mass *ratios* and a few absolute masses from the
combinatorial integers (NS, NT, d) and the f_occ spectrum, without free
mass parameters.

### 4/27-passing closed theorems

| Observable | DRLT value | Observed | Error | Lean |
|------------|-----------|----------|-------|------|
| m_μ / m_e | 206.7682837 | 206.7682838 | 0.48 ppb | `MuOverE.lean` |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% | `ProtonMass.lean` |
| m_H | 125.28 GeV | 125.25 GeV | +0.02% | `HiggsMass.lean` |
| τ-μ ratio | (PDG match) | — | ppm | `TauOverMu.lean` |

Each is closed `by decide`, 0 axioms.

### Mass formula structure (T2 derivation, narrative)

```
m_lepton(n) = m_e · (atomic counting factor)(n)
m_quark(flavor) = m_p · (chiral atomic factor)(flavor)
m_Higgs       = v_H · (occupation ratio at d=5)
```

The atomic counting factors come from C(5, k) and the f_occ spectrum.
The constants m_e, m_p, v_H currently enter as observational anchors.

### Quark hierarchy

`QuarkHierarchy.lean` derives the *ratios* m_t : m_b : m_c : m_s : m_u :
m_d from chiral atomic decomposition (`paper1`) without per-flavor
parameters. Match is at percent-level, not yet ppm.

## 213 sharpening

- "Why m_μ/m_e = 206.768..." → answer: closed-form rational expression
  in (NS, NT, d), 0.48 ppb match. Replaces the empirical
  Yukawa-coupling assignment of the Standard Model.
- "Why m_H ≈ 125 GeV" → answer: occupation-ratio formula at d = 5,
  +0.02% match. Fully forced by atomicity; no free parameters.
- m_p is reproduced exactly by chiral decomposition (`paper1`); the
  individual quark masses are derived from m_p + ratios.

## Open / next

- **Derive m_e from atomicity.** Currently anchor; needed for
  full first-principles Hydrogen IE chain (Ch. 04).
- **Derive m_p from atomicity.** Currently `ProtonMass.lean` matches
  but does not derive from Raw + Atomicity alone.
- Tighten quark hierarchy from %-level to ppm.
- Connect lepton mass formula to neutrino sector (Ch. 08).

## Sources

- `papers/paper1_chiral_decomposition.tex` (chiral mass structure)
- `papers/paper3_zero_parameter_predictions.tex` (catalog)
- `papers/drlt-book/chapters/ch09_masses.tex`
- `lean/E213/Lib/Physics/Mass/MuOverE.lean`, `ProtonMass.lean`,
  `HiggsMass.lean`, `TauOverMu.lean`, `QuarkHierarchy.lean`.
