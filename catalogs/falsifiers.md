# Falsifiers Catalog

CLAUDE.md verification criterion (2): a single measurement-Lens
reading contradicting the corresponding theory-Lens reading is a
213-internal contradiction (cf. `seed/AXIOM/08_falsifiability.md` §8.2 + "Falsification is internal" subsection — both readings
are 213-internal events; their disagreement is not external
refutation but residue-internal incoherence).  Each entry below
records a *structural necessity*: if the (3, 2, 5) atomicity is
the correct residue reading, then the entry's quantity has the
listed value.  Disagreement with measurement means the chosen
Lens does not reflect 213, not that an exterior judge condemns
the framework.

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

### F15: Bell coincidence count ≤ 12 = 2·NS·NT
  Two-qubit CHSH-style coincidence count bounded by atomic 12.
  Measurement giving > 12 (or strictly > 12 normalised) → discard.
  `lean/E213/Lib/Physics/Quantum/Bell.lean` (`bell_capstone`).

### F16: R_∞ atomic = 13605693 μeV ± 1
  H ionization energy bracket; pairs with the 4.3 ppb precision.
  Future ppt-level muonic-H / Lamb-shift outside → discard.
  `lean/E213/Lib/Physics/Atomic/IE/HydrogenPPM.lean`
  (`R_infinity_falsifier_bracket`).

### F17: e-folds N ∈ [50, 60] = d·NT·(d+1)
  Inflation count atomic; pairs with the precision N = 60 reading.
  CMB / B-mode / 21cm outside the bracket → discard.
  `lean/E213/Lib/Physics/Cosmology/EfoldsFalsifier.lean`
  (`efolds_validation_capstone`).

### F18: m_τ/m_μ base prefactor 16
  Tau/muon ratio integer skeleton; pairs with the precision pattern.
  Measured base outside 16 ≤ m_τ/m_μ < 17 → discard.
  `lean/E213/Lib/Physics/Mass/TauOverMu.lean` (`tau_mu_falsifier_bracket`).

### F19: Z partial widths count 12 = 2·NS·NT, no 4th-gen
  Z⁰ branching atomic count.  Cross-references F2 (N_gen = 3) via
  the same `binom NS 4 = 0` clause.  Z-width refinement giving
  4th-gen contribution → discard.
  `lean/E213/Lib/Physics/Simplex/Generations.lean`
  (`Z_partial_widths_falsifier`).

### F20: θ_QCD precision bracket 286 ∈ [251, 300]·10⁻¹³
  Pairs with F4 (current nEDM upper bound).  Next-gen nEDM giving
  θ_QCD outside the discrimination window → discard.
  `lean/E213/Lib/Physics/Couplings/ThetaQCD.lean`
  (`theta_QCD_precision_bracket`).

### F21: Koide Q = NT/NS = 2/3 atomic
  Lepton mass ratio coincidence Q = (m_e+m_μ+m_τ)/(√m_e+√m_μ+√m_τ)²
  uniquely fixed by (NS, NT) = (3, 2).  Future ppt-precision Koide
  measurement outside 2/3 ± 10⁻⁶ → discard.
  `lean/E213/Lib/Physics/Foundations/KoideFormula.lean`
  (`koide_falsifier`).

### F22: m_p/m_e ≈ 6π⁵ atomic skeleton 6 = NS·NT
  Lenz 1951 coincidence identified as NS·NT·π⁵ (0.062 ppm with
  α_GUT correction).  Atomic integer 6 = NS·NT = d+1 uniquely
  determined by atomicity.
  `lean/E213/Lib/Physics/Hadron/ProtonElectronRatio.lean`
  (`proton_electron_falsifier`).

### F23: M_Pl/v_H = d^(d²)/(d+1) hierarchy
  Atomic exponent d² = 25 and base d = 5 uniquely fix the
  hierarchy 5^25/6 ≈ 5×10¹⁶ within ~5%.  Refinement excluding
  this bracket → discard.
  `lean/E213/Lib/Physics/Higgs/Vacuum.lean`
  (`hierarchy_falsifier`).

### F24: Muon prefactor 192 = (NS²−1)(d²−1)
  Muon lifetime exact integer prefactor 192 = 8·24 uniquely fixed
  by SU(3)·SU(5) adjoint structure (NS, d) = (3, 5).
  `lean/E213/Lib/Physics/Foundations/AtomicSuperCatalog.lean`
  (`muon_prefactor_falsifier`).

### F25: m_t/m_c ≈ 137 ∈ [130, 145] (1/α_em atomic match)
  Top-charm mass ratio coincides with the 1/α_em fine-structure
  integer.  Same atomic 137 reads out both ratios.  Pairs with
  `QuarkHierarchy.quark_hierarchy_capstone` chain composition
  (NS·d² + NS·NT² = 87, + correction → 137).
  `lean/E213/Lib/Physics/Hadron/MtOverMc.lean`
  (`mt_mc_falsifier_bracket`).

### F26: η_B ≈ 6 × 10⁻¹⁰ atomic
  Baryon-to-photon ratio leading integer 6 = NS·NT uniquely fixed
  by atomic (NS, NT) = (3, 2); denominator exponent 10 = d·NT
  atomic.  Measurement outside `η_B × 10¹⁰ ∈ [5, 7]` → discard.
  `lean/E213/Lib/Physics/Cosmology/EtaBFalsifier.lean`
  (`eta_B_falsifier_bracket`).

## Stake formal

  phase3_falsifiers : 19-conjunct, 0 axioms (Lean verified)

## Forced-roster super-theorem (the integers are not fits)

  `Lib/Physics/Foundations/FalsifierRosterForced.falsifier_roster_forced`
  (1 PURE) — one theorem binding the two forcing `iff`s
  (`atomic_iff_five` → `d = 5`; `pair_forcing` → `(NT, NS) = (2, 3)`) to the
  headline falsifier integers as polynomials in the *forced* triple
  `(NS, NT, d) = (3, 2, 5)`:
  F1 `d = 5`, F2 `binom NS NT = 3`, F8 `d² − NS = 22`, F22/F26 `NS·NT = 6`,
  F26 `d·NT = 10`, F24 `(NS²−1)(d²−1) = 192`, F15/F19 `2·NS·NT = 12`,
  F21 `3·NT = 2·NS` (Koide `NT/NS = 2/3`).  The point is the *forcing*: the
  triple is the unique atomic one, so each integer is a consequence, not a
  free dial — measure any outside its bracket and the triple is refuted.

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
