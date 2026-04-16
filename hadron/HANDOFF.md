# Hadron Spectroscopy — Handoff

## Status: CLOSED (1차) ★★★ — 9 Experiments

## Key Results (0 free parameters)

| Observable | DRLT | Observed | Error | Formula |
|-----------|------|----------|-------|---------|
| m_π | 137.6 MeV | 137.3 MeV | **+0.2%** | √(n_eff Σm_q Λ) |
| m_ρ | 782.1 MeV | 775.3 MeV | **+0.9%** | √(m_π²+Δ²) |
| m_ω | 782.1 MeV | 782.7 MeV | **-0.07%** | √(m_π²+Δ²) |
| m_K | 498.2 MeV | 493.7 MeV | **+0.9%** | √(n_eff(m_u+m_s√σ)Λ) |
| m_K* | 915.7 MeV | 891.7 MeV | +2.7% | √(m_K²+Δ²) |
| m_φ | 1053.9 MeV | 1019.5 MeV | +3.4% | √(m_ss²+Δ²) |
| m_J/ψ | 3081.6 MeV | 3096.9 MeV | **-0.5%** | √(m_ηc²+Δ²) |
| m_Υ | 9430.5 MeV | 9460.3 MeV | **-0.3%** | √(m_ηb²+Δ²) |
| Δ-N | 295.7 MeV | 294 MeV | **+0.6%** | Λ×(d²-1)/d² |

## Core Formulas

```
Pseudoscalar (GMOR):  m_PS² = n_eff × Σm_q × Λ_QCD
                      n_eff = C(d,3) - 1 = 9

Hyperfine (V-PS):     m_V² = m_PS² + Δ²
                      Δ = dΛ/N_T = 5×308/2 = 770 MeV

Baryon spin:          m_Δ - m_N = Λ × (d²-1)/d² = Λ×24/25

Kaon correction:      m_s → m_s × √σ_cross (σ = 7/8 from atoms/)
```

## Derivation Chain

```
d=5 → n_eff=C(5,3)-1=9 → GMOR: m_PS²=9×Σm_q×Λ → m_π +0.2%
                        → hyperfine: Δ=dΛ/N_T=770 → m_V RMS 1.8%
    → (d²-1)/d²=24/25 → baryon spin: Δ-N +0.6%
    → σ_cross=7/8 (atoms) → kaon: m_K +0.9%
```

## Method Discovery (HAD_004→005)

**"그림만 그리고 관찰"** 이 최선의 접근이었음:
- HAD_001-003: 공식 피팅 → RMS 20-35%
- HAD_004: 심플렉스에 하드론 그리기 → det(G) 패턴 발견
- HAD_005: det 관찰 → m_V²=m_PS²+Δ² 발견 → **RMS 1.8%**

## Experiments
| ID | Title | Key Result |
|----|-------|-----------|
| HAD_001 | Meson spectrum | m_π +0.2%, Δ-N +0.6% |
| HAD_002 | Error analysis | 4 geometric origins |
| HAD_003 | Corrected spectrum | K +0.9%, η_c -5.9% |
| HAD_004 | Draw hadrons | det(G) pattern discovery |
| HAD_005 | Unified mass | m_V²=m_PS²+Δ², RMS 1.8% ★★★ |
| HAD_006 | Complete rational spectrum | median 3.5%, 14/20 within 5% |
| HAD_007 | Pure Gram algorithm | theoretical insight on limits |
| HAD_008 | Condensate Gram | condensate, GMOR, hyperfine from ONE matrix |
| HAD_009 | A-vertex recoil | median 3.5%→1.9%, Ω⁻ +9.9%→-0.2% ★★★ |

## Open (정밀화)
1. η/η' mixing angle from Gram off-diagonal
2. φ +3.4% — strange sector correction
3. Baryon octet masses (Σ, Ξ, Ω) systematic
4. Heavy meson absolute masses (D, B)

## Next: HAD_010
