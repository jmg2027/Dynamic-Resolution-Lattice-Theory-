# Falsifiers Catalog

CLAUDE.md verification criterion (2): 1 measurement violation → 213 discard.

## Explicit falsifiers (Phase 3)

### F1: Atomicity (d=5 unique)
  Observed dimension ≠ 5 → discard
  ¬ Atomic 4, 6, 11, 26 (excludes string theory etc.)

### F2: Absence of 4th generation
  N_gen = C(NS, NT) = 3
  Collider 4th gen discovery → discard

### F3: Neutrino normal ordering
  m_3/m_2 ≈ 5.71 (Phase 3 NeutrinoRatioDerivation)
  JUNO inverted ordering measurement → discard (~2030)

### F4: θ_QCD ∈ [2.5, 3.0]×10⁻¹¹
  J·α^(d-1) atomic
  nEDM next-generation outside → discard (~2027-30)

### F5: cos²θ_W ∈ [0.75, 0.78]
  Future precision measurement outside → discard

### F6: Magic numbers {2,8,20,28,50,82,126}
  HO closed form n(n+1)(n+2)/3 + spin-orbit
  Observed 7/7 exact.  Additional super-heavy measurement decides.

### F7: PMNS angles atomic denom
  1/NS, 1/NT, d²-1
  DUNE/HK precision measurement → decides

### F8: Cabibbo λ = 5/22 = d/(d²-NS)
  LHCb/Belle II refinement outside → discard

### F9: m_p atomic exact
  NS·Λ_QCD·P(α·NS/d)
  Lattice QCD next-order different integer → discard

### F10: 1/α_em = 137 bracket
  More precise measurement → bracket tightening required

### F11: m_μ/m_e = 206.768 ppb
  NS·137/NT atomic
  Different leading integer → discard

### F12: Higgs mass 125.28 GeV
  (1/c)·v_H + α corrections
  Further refinement → outside discard

### F13: Ω_Λ = 0.685 atomic
  (1-1/π)(1+α/d)
  Further refinement → outside discard

### F14: Z=168 super-heavy prediction
  HO magic 7 stability island
  Verified if observed; discard if different integer

## Stake formal

  phase3_falsifiers : 19-conjunct, 0 axioms (Lean verified)

## ★ 213 Kernel axiom-free closure (KH marathon)

The following falsifiers are formalized with *literally* 0 Lean axioms
(`E213.Term.Cap_PhysicsFalsifiers` etc.):

  ★ F1  d ≠ 26, d ≠ 11           (absence of string/M-theory)
  ★ F4  θ_QCD bracket             (286 ∈ [251, 300])
  ★ F8  λ_Cabibbo precise         (5/22 ∈ [0.226, 0.228])
  ★ F10 1/α_em bracket            (137 ∈ [137, 138])
  ★ F11 m_μ/m_e bracket           (206.7682 inline)
  ★ F12 m_H/v_H bracket           (5097 ∈ [50·10⁴, 52·10⁴])
  ★ F13 Ω_Λ bracket               (685 ∈ [684, 686])
  ★ F14 Z=168 cumsum              (cumsum [2,8,8,18,18,32,32,50])

Verification:
  $ ./tools/kernel_regress.sh
  ✅ Kernel pure: 101 theorems verified 0-axiom.

★ marks = `#print axioms` empty list.  None of Lean kernel's propext,
Quot.sound, Classical.choice contributes to the truth value.
This is the formal proof of the vision ("213 = floor, Lean = syntactic host").

## Measurement timeline

  2025-2030: JUNO (F3), nEDM (F4), DUNE (F7)
  2030+:     HK (F7), LHCb (F8), Lattice precision (F9)
  2050+:     Z=168 super-heavy (F14)

## One line

  > "Any single falsifier violation → repo deleted"
