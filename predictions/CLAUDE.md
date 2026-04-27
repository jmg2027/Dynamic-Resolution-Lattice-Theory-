# Testable Predictions Sub-Project

> 아직 측정되지 않은 DRLT 예측 모음.
> **이론 검증의 핵심.** known observables를 맞추는 것은 retrodiction,
> unknown observables를 예측하는 것이 진짜 test.

## Scope
- 미측정 예측값 계산 및 검증 전략
- 향후 실험과의 비교 (JUNO, HL-LHC, nEDM, DESI 등)
- SM/BSM 이론과의 구별력 분석

## Key Predictions

| Observable | DRLT | Current | Future Exp | Timeline |
|-----------|------|---------|-----------|----------|
| ν m₃/m₂ | 5.712 | 5.71±0.12 | JUNO | 2025-27 |
| m_H | 125.28 GeV | 125.25±0.17 | HL-LHC | 2029+ |
| θ_QCD | J×α⁴≈2.86×10⁻¹¹ | <1.8×10⁻¹⁰ | nEDM next-gen | 2027-30 |
| N_gen | exactly 3 | 3 observed | FCC-ee/hh | 2035+ |
| λ_H | 0.1299 | ~0.129 | di-Higgs | 2030+ |
| δ_CKM | 68.75° | 65.4±3.2° | LHCb/Belle II | 2025-28 |
| w(z) | -1 exact | ~-1±0.05 | DESI/Euclid | 2025-28 |

## Experiment Map
```
PRD_001: Neutrino mass ratio (JUNO prediction)      7/7 ✓
PRD_002: Higgs mass precision (HL-LHC prediction)   4/4 ✓
PRD_003: θ_QCD (nEDM prediction)                    5/5 ✓
PRD_004: Generation count = 3 (no 4th gen)           5/5 ✓
PRD_005: Complete prediction catalog                  4/4 ✓
PRD_006: θ_QCD precision derivation                   7/7 ✓ (SUPERSEDED by PRD_007)
PRD_007: θ_QCD rigorous Berry phase                   9/9 ✓ (best candidate: J×α⁴)
PRD_008: Variational θ — S₃ axiomatic                3/4 (1 expected fail)
PRD_009: Berry phase = spectral flow (U(1))          11/11 ✓ ★
PRD_010: Muon g-2 structural reading                  9/9 ✓ ★
PRD_011: Muon g-2 pure DRLT (no SM imports)            9/9 ✓ ★
```

## Muon g-2 (PRD_010) — DRLT reading
- Schwinger α/(2π) 정확, EW(1-loop) DRLT v_H + sin²θ_W
- a_μ^DRLT(BMW HVP) = 116_591_954 × 10⁻¹¹
- a_μ^SM (BMW lit)   = 116_591_953 × 10⁻¹¹  (차 +1)
- a_μ^exp (Fermilab) = 116_592_059 × 10⁻¹¹  (DRLT 대비 −1.72σ)
- R-ratio path: −5.13σ (구조적으로 SM HVP 분기 산물 추정)
- DRLT 베팅: no anomaly. m_μ/m_e ppb 정합성 + N_gen=3가 BSM 거부
- Falsifier: R-ratio HVP가 lattice와 영구 불일치 + Fermilab 영구 5σ

## PRD_011 — Pure DRLT (no SM imports)
- 입력: α_em, α_GUT, α_3, v_H, sin²θ_W, m_μ, m_p, Λ_QCD,
  m_π, m_ρ, Δ_hyp 모두 DRLT 0-param 또는 명시 ansatz (f_π=Λ/π)
- a_μ^DRLT(pure) = 116_416_326 × 10⁻¹¹  (-0.15% vs exp)
- Schwinger ✓ exact, EW 1-loop ✓ DRLT inputs,
  HVP via KSRF VMD ✓ 차수, HLBL OoM ✓
- Gap (-1507 ppm) = QED 2..5-loop C_n 누락 (DRLT-Dyson은
  C_1 exact + C_2 부분만 capture, C_3..C_5 미반영)
- 다음: f_occ 다중루프 카운팅으로 C_n 도출, R(s) 적분

## θ_QCD 유도 이력
- PRD_003: 초기 추정 J×α⁴ ≈ 2.86×10⁻¹¹
- PRD_006: α⁶sin(π/12) ≈ 5.4×10⁻¹¹ 시도 → **폐기** (sin(π/12) 비정당화)
- PRD_007: Berry phase 엄밀 분석 → J×α⁴ ≈ 2.86×10⁻¹¹ **확정**
- PRD_008: S₃ 대칭은 Regge 동역학이 아닌 공리(Frobenius+chirality)에서 부과됨
- PRD_009: Berry phase ≡ U(1) spectral flow, Chern number = 0 (상쇄의 위상학적 보호)

## Status: ACTIVE
총 71/72 checks passed. 11개 실험 완료.
다음: PRD_012 또는 QED C_n DRLT 도출 (PRD_011 후속).
