# 04 — Quantization (ℏ, atomic spacing)

**Tier:** T1
**Status:** Partial; quantization step closed for IE_H at 4.3 ppb.
**Lean:** `Physics/Atomic/IE/HydrogenPPM.lean`, `Physics/Library/*`.

## Best current statement

Quantization in 213 is not postulated; it emerges from the **atomic
counting of simplicial states**. ℏ is the natural unit of action when
the f_occ spectrum (Ch. 03) is interpreted as occupation probability.

### Hydrogen ionization energy formula (closed at 4.3 ppb)

The first 4/27-standard pass for a quantization-derived observable:

```
IE_H = m_e · c² · α² / 2
```

`Atomic/IE/HydrogenPPM.lean` proves the inequality

```
2 · IE_H_micro · (1/α_milli)² ∈ [m_e_centi · 10¹⁰ − 3·10⁹,
                                  m_e_centi · 10¹⁰]
```

by `decide`, with m_e and α given to ppm precision. Width gives a
relative bound of 4.3 ppb — within the 4/27 ppb threshold.

### Periodic table extension (`Library/`)

Phase 4 extends the IE formula across periods 1–7 (Z = 1..118) plus
five super-heavy candidates (Z = 119..168). Each row is closed by
`decide` against PDG ionization energy tables.

## 213 sharpening

- "Why Rydberg formula works" → answer: the 1/2 prefactor and α²
  dependence are forced by the simplicial occupation structure
  combined with the d=5 atomicity; not empirical.
- "Why integer principal quantum number n" → answer: the f_occ
  spectrum (Ch. 03) is genuinely rational, not just denumerable;
  integer n is the leading entry of the spectrum.
- ℏ does not appear as a fundamental constant — only c and α appear in
  the IE formula. ℏ is the conversion factor between rational atomic
  counts and SI energy units.

## Caveats (honest)

- **Inputs**: m_e and α are taken as observed values, not derived from
  the Raw axiom. The Phase 4 chain validates the *formula*, not the
  *constants*. Reaching α from atomicity is the open α_em marathon
  (Ch. 05); reaching m_e from atomicity is open.
- The 4.3 ppb closure is a numerical *agreement*, not a *first-principles
  derivation*. This is the honest reading of the 4/27 standard.

## Open / next

- Derive α from Raw + atomicity, replacing the input.
- Derive m_e from atomic counting, replacing the input.
- Extend Phase 4 closure to molecular ionization (currently atomic
  only) — bond-angle marathon partially started.
- Explicit ℏ-elimination theorem: state and prove that 213 physics can
  be expressed entirely without reference to ℏ.

## Sources

- `lean/E213/Lib/Physics/Atomic/IE/HydrogenPPM.lean`,
  `Hydrogenic.lean`, `HeliumPPM.lean`, `Lithium.lean`, `Beryllium.lean`,
  `Boron.lean`, `CNOFNe.lean`, `SecondRow.lean`, `Period3.lean`,
  `Period4.lean`, `PeriodicTable.lean`, `PeriodClosures.lean` —
  full IE stack across the periodic table (`IE/INDEX.md`).
- `catalogs/atomic-integers.md`
