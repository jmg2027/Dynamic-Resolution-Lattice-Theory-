# 213 Master Guide — Status

## Tier distribution

```
Total chapters       : 16  (Ch. 00–15 + 2 appendices)

T0  (213-internal only)    : 4   (Ch. 00, 02, 14, 15)
T1  (213 sharper)          : 5   (Ch. 03, 04, 07, 11, 14)
T2  (classical adequate)   : 5   (Ch. 05, 06, 08, 09, 10)
T3  (classical only)       : 1   (Ch. 13)

Hybrid tags (T0/T3, T1/T3, T2/T1, etc.) span chapters that bridge
multiple tiers per section.
```

## 4/27 standard pass-list (closed Lean theorems at ppb~ppm)

| # | Observable | Precision | Lean module | Guide |
|---|-----------|-----------|-------------|-------|
| 1 | IE_H = m_e·c²·α²/2 | 4.3 ppb | `Atomic/IE/HydrogenPPM` | Ch. 04 |
| 2 | m_μ / m_e | 0.48 ppb | `Mass/MuOverE` | Ch. 06 |
| 3 | m_p | exact | `Hadron/ProtonMass` | Ch. 06 |
| 4 | m_H | +0.02% | `Higgs/Mass` | Ch. 06 |
| 5 | sin² θ₁₃ | −0.07σ | `Mixing/NeutrinoMixing` | Ch. 08 |
| 6 | m₃ / m₂ (ν) | +0.04% | `Mixing/NeutrinoMixing` | Ch. 08 |
| 7 | Ω_Λ | 0.0008% | `Cosmology/DarkEnergy` | Ch. 09 |
| 8 | Magic numbers 7/7 | exact | `Nuclear/MagicNumbers` | Ch. 11 |
| 9 | d = 5 atomicity | exact (theorem) | `Theory/Atomicity/Five` | Ch. 02 |
| 10 | 1/α₃ = 8 | exact | `PhotonKernel` | Ch. 05/Ch. 10 |
| 11 | Periodic table Z=1..118 | ppb-level | `Library` | Ch. 07 |
| 12 | CH₄/H₂O/NH₃ angles | exact | `BondAngles` | Ch. 07 |
```

12 closed lines with 4/27 standard met.
```

## Pending list (numerical match exists; not yet ppb closed)

| Observable | Current state | Target | Guide |
|-----------|---------------|--------|-------|
| 1/α_em = 137.036 (1a) | tight bracket [N=20] width 0.14, [N=50] width 0.024 | width < 10⁻⁴ | Ch. 05 |
| 1/α_em = 137.036 (1b) | gap 5.443×10⁻⁴ → reframed: missing simplicial invariant | Cohomology 213 marathon (Phase CE) | Ch. 05 |
| Cohomology 213 marathon | **CLOSED + Audit/Bridge + Chiral + L-Fractal + TopologyCompare** (23 files, ~85 theorems, 0 axiom). | Paper 1/2/3 reconstruction continues | Ch. 14 |
| **Linalg213 marathon** | **CLOSED (L1-L6)** (7 files, ~32 theorems; legacy ≤ {propext, Quot.sound} closure — now sorry-equivalent under the ∅-axiom standard, queued for retirement). ★★★ `paper1_chiral_compression` capstone bundles atomicity + Linalg chiral split + Cohomology bigrading + Bridge + Physics b_1=8 + topology uniqueness. | retire propext leaks | Ch. 14 |
| α_GUT = 6/(25π²) | bracket [N=3] width ~8 | width < 10⁻⁴ | Ch. 05 |
| AlphaEM/V137 d²/NS=25/3 | conjectural-tagged | derive from Raw | Ch. 05 |
| η_B | 0.5% narrative | ppb | Ch. 09 |
| Cabibbo λ = 5/22 | bracket only | ppm | Ch. 08 |
| YM mass gap (continuum) | statement closed | full proof | Ch. 12 |
| m_π, m_ω, m_J/ψ, Δ-N | sub-percent | ppm | Ch. 10 |
| Bethe-Weizsäcker a_V/a_S/a_C | percent | ppm | Ch. 11 |
| Quark hierarchy | percent | ppm | Ch. 06 |
| RH and Millennium-class | external-only | first Lean | Ch. 13 |

## Falsifiers (binding — 7 from `seed/AXIOM/08_falsifiability.md`)

1. Neutrino ordering (JUNO ~2030) — pending
2. θ_QCD bracket (next-gen nEDM 2027–30) — pending
3. 4th generation (LHC ongoing) — passing so far
4. PMNS angle deviations — passing
5. Cabibbo λ refinement — passing
6. Proton mass — passing
7. Magic numbers — passing (7/7 exact)

`tools/kernel_regress.sh` enforces 0-axiom invariant on every Kernel
edit. `tools/FORBIDDEN.md` blocks `sorry`, `axiom`, `import Mathlib`,
`open Classical`, `native_decide` in `lean/E213/Term/*.lean`.

## Update protocol

Updated when: marathon closes a theorem; new module appears;
falsifier observed; chapter tier migrates. Sync `INDEX.md`,
chapter files, `appendix_lean_map.md`, `catalogs/falsifiers.md`.
