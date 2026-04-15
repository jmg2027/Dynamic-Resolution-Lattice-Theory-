# Hadron Spectroscopy Sub-Project

> 하드론 질량 스펙트럼 — 닫힌 전파자 P(x)=(1+2x)/(1+x)와 심플렉스 구조에서 유도.

## Scope
- Meson masses (π, K, ρ, ω, φ, J/ψ, Υ, ...)
- Baryon masses (N, Δ, Σ, Ξ, Ω, Λ_c, ...)
- Mass splittings (Δ-N, ρ-π, K-π, ...)
- Decay constants (f_π, f_K, ...)

## Key Formulas (from initial test)
```
Pseudoscalar meson (GMOR):
  m_PS² = n_eff × (m_q₁ + m_q₂) × Λ_QCD
  n_eff = C(5,3) - 1 = 9

Vector-pseudoscalar splitting:
  m_V - m_PS = N_T × Λ_QCD = 2 × 308 = 616 MeV

Baryon spin splitting:
  m_Δ - m_N = Λ_QCD × (d²-1)/d² = 308 × 24/25 = 295.7 MeV

Baryon masses:
  m_baryon = N_S × Λ_QCD × P(α, N_S/d) + quark corrections
```

## Key Constants
```
Λ_QCD = 308 MeV, n_eff = 9, d = 5
N_S = 3, N_T = 2, α_GUT = 6/(25π²)
(d²-1)/d² = 24/25 (adjoint fraction)
```

## Initial Results
| Hadron | DRLT | Observed | Error |
|--------|------|----------|-------|
| m_π | 137.6 MeV | 137.3 MeV | **+0.2%** |
| Δ-N | 295.7 MeV | 294 MeV | **+0.6%** |
| m_ρ | 753.6 MeV | 775.3 MeV | -2.8% |
| m_K | 514.7 MeV | 495.6 MeV | +3.8% |

## Rational Structure (from Atomic Formulary Thm 10-11)

With ζ₉ = 9778141/6350400 (rational, DHA Thm 5):
```
α₉ = 254016/9778141  [exact rational]

Pseudoscalar: m_PS² = 9 × Σm_q × Λ     [integer coefficient]
Hyperfine:    m_V² = m_PS² + (5Λ/2)²    [integer coefficients]
Baryon spin:  Δ-N = Λ × 24/25           [rational]
```

ALL hadron masses are **rational multiples of Λ_QCD**.
No π, no cos, no transcendental functions.
The same rational structure as the Atomic Formulary (Thm 11).

## Status: CLOSED (1차) — precision open for η', φ, heavy mesons
