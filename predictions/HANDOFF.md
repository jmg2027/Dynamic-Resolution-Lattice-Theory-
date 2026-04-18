# Testable Predictions — Handoff

## Status: ACTIVE (8 experiments, 48/49 checks; PRD_006 superseded by PRD_007)

## Completed Experiments
| ID | Title | Checks | Key Result |
|----|-------|--------|-----------|
| PRD_001 | ν mass ratio JUNO | 7/7 | m₃/m₂=5.712, JUNO에서 TBM과 81σ 분리 |
| PRD_002 | Higgs mass HL-LHC | 4/4 | 125.28 GeV, HL-LHC ±0.05 GeV |
| PRD_003 | θ_QCD nEDM | 5/5 | J×α⁴ ≈ 2.9×10⁻¹¹ best candidate |
| PRD_004 | N_gen = 3 | 5/5 | C(3,2)=3, 4세대 불가 |
| PRD_005 | Prediction catalog | 4/4 | 12 retrodictions, 7 testable predictions |
| PRD_006 | θ_QCD sin(π/12) | 7/7 | ★ SUPERSEDED by PRD_007 ★ |
| PRD_007 | θ_QCD rigorous | 9/9 | Berry phase 구조 해명 |
| PRD_008 | Variational θ | 3/4 | 단일 심플렉스로는 불충분 |
| PRD_009 | Berry spectral flow | 11/11 | ★ Berry phase = U(1) spectral flow |

## Key Findings — θ_QCD
PRD_007에서 밝혀진 구조:
1. **θ_bare = SSS holonomy = Berry phase (α에 무관!)**
   - CKM parameterization으로 계산: Φ ≈ -0.103 rad
   - 이것은 O(10⁻¹), O(α⁶)이 아님
   - δ=0 → Φ=0 (CP 보존이면 holonomy 없음) ✓
2. **θ_phys = θ_bare + arg(det Y_u Y_d)**
   - 둘 다 같은 Gram matrix에서 유래 → 변분원리가 상쇄 강제
   - 잔여의 정확한 차수와 계수 = OPEN PROBLEM
3. **최선 후보: θ_phys = J_CKM × α⁴ ≈ 2.86×10⁻¹¹**
   - J = 8.18×10⁻⁵ (DRLT Jarlskog invariant)
   - α⁴ = 3.50×10⁻⁷
   - bound (1.8×10⁻¹⁰)의 0.16배 → 안전
4. **PRD_006의 sin(π/12) 계수는 폐기** (사후 끼워맞춤)

## Critical Finding (PRD_008)
**Regge action은 S₃ 대칭을 강제하지 않는다.**
- 단일 심플렉스 최적화 → Φ_SSS = π/2 (mixing 최대화)
- S₃ 대칭은 공리에서 부과 (Frobenius + chirality)
- θ ~ α⁶은 **진공 평균** ⟨Φ_SSS⟩의 성질
- 단일 심플렉스에서는 Φ = O(1) (PRD_007 일관)

## Key Findings — Berry = Spectral Flow (PRD_009)
PRD_009에서 밝혀진 구조:
1. **arg(G₀₁G₁₂G₂₀) ≡ Pancharatnam Berry phase** (차이 = 0, 정확)
   - PRD_007이 '이미 암묵적으로 사용 중'이었던 구조
2. **Chern number = 0** (total Berry phase ≈ 10⁻⁸ rad)
   - 개별 고유상태: ±1.087 rad (큰 Berry phase, 서로 상쇄)
   - spectral flow = 0 → 위상학적으로 보호된 상쇄
3. **Index theorem 구조**:
   - θ_bare = Berry(SSS) = U(1) spectral flow of Gram matrix
   - arg(detY) = Berry(mass) = U(1) spectral flow of Yukawa sector
   - θ_phys = 전체 U(1) spectral flow의 잔여
   - S₃ 대칭 → tree-level 상쇄, 잔여 = J × α⁴
4. **왜 U(1)?**: θ는 위상 = U(1) 원소. Non-abelian → Wilczek-Zee.
   det(Yukawa)의 위상이므로 U(1) 사영.

## Open Problems
1. **θ_QCD 정밀 계수** — 다중 심플렉스 진공 또는 S₃-제약 섭동론 필요
2. Proton decay lifetime 계산
3. Neutron star max mass (simplex EOS)
4. 1/α_s tension (~5.5%)
5. sin²θ_W tension (~0.8%)

## Next Available Experiment
PRD_010
