# Falsifiers Catalog

CLAUDE.md 검증 기준 (2): 측정 1 위반 → 213 폐기.

## 명시적 falsifier (Phase 3)

### F1: Atomicity (d=5 unique)
  관측 차원 ≠ 5 → 폐기
  ¬ Atomic 4, 6, 11, 26 (string theory 등 배제)

### F2: 4th generation 부재
  N_gen = C(NS, NT) = 3
  collider 4th gen 발견 → 폐기

### F3: Neutrino normal ordering
  m_3/m_2 ≈ 5.71 (Phase 3 NeutrinoRatioDerivation)
  JUNO inverted ordering 측정 → 폐기 (~2030)

### F4: θ_QCD ∈ [2.5, 3.0]×10⁻¹¹
  J·α^(d-1) atomic
  nEDM 차세대 outside → 폐기 (~2027-30)

### F5: cos²θ_W ∈ [0.75, 0.78]
  미래 정밀 측정 outside → 폐기

### F6: Magic numbers {2,8,20,28,50,82,126}
  HO closed form n(n+1)(n+2)/3 + spin-orbit
  관측 7/7 정확.  추가 super-heavy 측정 결판.

### F7: PMNS angles atomic denom
  1/NS, 1/NT, d²-1
  DUNE/HK 정밀 측정 → 결판

### F8: Cabibbo λ = 5/22 = d/(d²-NS)
  LHCb/Belle II 정밀화 outside → 폐기

### F9: m_p atomic exact
  NS·Λ_QCD·P(α·NS/d)
  Lattice QCD next-order 다른 정수 → 폐기

### F10: 1/α_em = 137 bracket
  더 정밀 측정 → bracket tightening 필요

### F11: m_μ/m_e = 206.768 ppb
  NS·137/NT atomic
  다른 leading 정수 → 폐기

### F12: Higgs mass 125.28 GeV
  (1/c)·v_H + α corrections
  더 정밀화 → outside 폐기

### F13: Ω_Λ = 0.685 atomic
  (1-1/π)(1+α/d)
  더 정밀화 → outside 폐기

### F14: Z=168 super-heavy 예측
  HO magic 7 stability island
  관측 시 검증, 다른 정수면 폐기

## Stake formal

  phase3_falsifiers : 19-conjunct, 0 axioms (Lean 검증)

## 측정 timeline

  2025-2030: JUNO (F3), nEDM (F4), DUNE (F7)
  2030+:     HK (F7), LHCb (F8), Lattice 정밀 (F9)
  2050+:     Z=168 super-heavy (F14)

## 한 줄

  > "어느 한 falsifier 위반 → 레포 삭제"
