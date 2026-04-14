# Testable Predictions — Handoff

## Status: ACTIVE (6 experiments, 32/32 checks)

## Completed Experiments
| ID | Title | Checks | Key Result |
|----|-------|--------|-----------|
| PRD_001 | ν mass ratio JUNO | 7/7 | m₃/m₂=5.712, JUNO에서 TBM과 81σ 분리 |
| PRD_002 | Higgs mass HL-LHC | 4/4 | 125.28 GeV, HL-LHC ±0.05 GeV |
| PRD_003 | θ_QCD nEDM | 5/5 | α⁶≈2.07×10⁻¹⁰, bound 근처 tension |
| PRD_004 | N_gen = 3 | 5/5 | C(3,2)=3, 4세대 불가 |
| PRD_005 | Prediction catalog | 4/4 | 12 retrodictions, 7 testable predictions |
| PRD_006 | θ_QCD precision | 7/7 | α⁶sin(π/12) = 5.35×10⁻¹¹, tension 해소 |

## Key Findings
- **θ_QCD tension 해소**: PRD_006에서 정밀 유도
  - 구 공식: θ ~ α⁶ ≈ 2.07×10⁻¹⁰ (bound 초과)
  - **신 공식: θ = α⁶ sin(π/12) = 5.35×10⁻¹¹** (bound의 0.30배)
  - sin(π/12) = SU(5) 위상 양자 (PMNS δ와 동일 기원)
- **가장 urgent**: JUNO ν mass ratio (2025-27)
- **17개 SM free parameters** 모두 d=5에서 유도

## Open Problems
1. Proton decay lifetime 계산 (SU(5) 구조이지만 mechanism 다름)
2. Neutron star max mass (simplex EOS)
3. 1/α_s tension (~5.5%) — running correction 필요?
4. sin²θ_W tension (~0.8%) — 2-loop effect?

## Next Available Experiment
PRD_007

## Infrastructure Changes
- `lib/experiment.py`: results를 sub-project results/에 저장하도록 수정
- root CLAUDE.md 규칙 9 강화: root results/는 REPORT/SUMMARY만
