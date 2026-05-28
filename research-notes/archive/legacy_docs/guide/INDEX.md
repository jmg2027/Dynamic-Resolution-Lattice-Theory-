# 213 Master Guide — Index

## Chapter map

| # | Chapter | Tier | 4/27 standard | Primary Lean | Primary paper |
|---|---------|------|---------------|--------------|---------------|
| 00 | Meta — what 213 is | T0 | n/a (foundation) | Theory/Raw, Theory/Atomicity/Five | paper14, drlt-book ch22 |
| 01 | Substrate — Raw to ℂ-like | T0/T3 | n/a (axiom + classical) | Theory/Raw, Meta/SelfRecognising | paper1, paper2, ch01 |
| 02 | Atomicity — d=5, NS=3, NT=2, Fibonacci | T0 | passing (theorem) | Theory/Atomicity/Five, Lib/Physics/Foundations/FibonacciAtomic | paper1, ch02-ch03 |
| 03 | Simplex geometry & hinges | T1 | passing | Physics/Simplex/Counts, Physics/Simplex/FaceTerms | paper6, ch04-ch06 |
| 04 | Quantization (ℏ, atomic spacing) | T1 | partial | Physics/Atomic/IE | ch07 |
| 05 | Coupling constants (α_GUT, α_em, α_3) | T2 | partial (bracket only) | Physics/Couplings/AlphaGUT, Physics/AlphaEM/V137 | paper2, paper4, paper6, ch08 |
| 06 | Mass spectrum (lepton, quark, Higgs) | T2/T1 | passing for m_μ/m_e, m_p, m_H | Physics/Mass/MuOverE, ProtonMass, HiggsMass | ch09 |
| 07 | Atomic structure & periodic table | T1 | passing for Z=1..118 | Physics/Library/* | ch10, ch20 |
| 08 | Mixing (CKM, PMNS) | T2 | partial | Physics/CabibboAngle, NeutrinoMixing | ch11 |
| 09 | Cosmology (Ω_Λ, η_B, Webb) | T2/T3 | passing for Ω_Λ | Physics/DarkEnergy | ch13, ch17 |
| 10 | Hadron spectrum | T2 | passing for m_π, m_ω | Physics/HadronMasses | ch19 |
| 11 | Nuclear (magic, binding) | T1 | passing for magic 7/7 | Physics/Nuclear/MagicNumbers, NuclearBinding | ch16 |
| 12 | Yang–Mills & gauge | T1/T3 | partial (mass gap statement) | Physics/YangMillsGap | paper8, ch15 |
| 13 | Critical line & RH | T3/T2 | not yet | (none) | paper5, paper7, paper9 |
| 14 | Cohomological calculus | T0/T1 | passing (analysis213) | Research/Real213/Flux* | (new — not in papers) |
| 15 | Metalogic — R1–R4 & falsifiability | T0 | passing | Meta/SelfRecognising, Tactic/VerifyR4 | seed/AXIOM, FALSIFIABILITY |
| A1 | Paper origins (reverse map) | — | — | — | — |
| A2 | Lean module map | — | — | — | — |

## Tier distribution

```
T0  : 4 chapters  (00, 02, 14, 15)
T1  : 5 chapters  (03, 04, 07, 11, partial 06/12)
T2  : 5 chapters  (05, 08, 09, 10, partial 06/12)
T3  : 1 chapter   (13)
```

## 4/27 standard pass-list (closed Lean theorems matching observation at ppb~ppm)

1. IE_H = m_e·c²·α²/2 → 4.3 ppb closed (Physics/Atomic/IE/HydrogenIEPPM)
2. m_μ/m_e → 0.48 ppb closed (Physics/Mass/MuOverE)
3. m_p → 0.000% closed (Physics/ProtonMass)
4. Ω_Λ → 0.0008% closed (Physics/DarkEnergy)
5. Magic numbers 7/7 → exact closed (Physics/Nuclear/MagicNumbers)
6. Periodic table Z=1..118 → ppb-level closed (Library)
7. d=5 atomicity → exact theorem (Theory/Atomicity/Five)

## 4/27 standard pending list (claims not yet closed at standard)

- 1/α_em → tight bracket [N=20] width 0.14, [N=50] width 0.024.
  Intrinsic gap 5.443×10⁻⁴ to observed 137.036 reframed as the
  motivation for the **Cohomology 213 marathon** (next priority,
  blueprint `blueprints/math/15_cohomology_213*`).
  Sixth simplicial invariant candidate to be enumerated in Phase CE.
- α_GUT → bracket containing 41 at N=3, width ~8
- AlphaEM/V137 d²/NS = 25/3 term → conjectural structural form
- sin²θ₁₃, m₃/m₂, m_H/v_H → numerical match, not yet bracketed
- η_B → 0.5% match, not yet formal
- Yang–Mills mass gap → statement formalized, full proof open
- All Millennium-class results in Ch.13

See `STATUS.md` for the up-to-date counts.
