# CAPSTONE INDEX — 213 master theorems organized

Quick navigation for major Lean capstones.  Updated 2026-05-01.

## Top-level achievements

### Validation Standard satisfied (root)
- `Physics/ValidationStandardOne.validation_standard_capstone`
  — CLAUDE.md #1+#2 explicit, 13 conjuncts, STRICT 0-AXIOM

### Pure atomic closure (strongest)
- `Physics/PureAtomicObservables.pure_atomic_observables_capstone`
  — 17 conjuncts, no N_U dependence, pure rational

## Finitist N_U chain (Standard #1)

### α_em chain
- `Physics/AlphaEMSO10.alpha_em_so10_capstone` — 4 ppm → 15 ppb
- `Physics/AlphaEMGramSelfEnergy.alpha_em_gram_capstone` — 15 ppb → 0.18 ppb
- `Physics/AlphaEMMasterCapstone.alpha_em_master_capstone` — 8-conjunct master

### N_universe identification
- `Physics/NUniverseFromFractal.n_universe_atomic_decomposition`
- `Physics/NUniverseFractalDepth.n_universe_self_consistent`
  — L = d² self-referential
- `Physics/FractalLensCardinality.fractal_lens_cardinality_capstone`
  — Lens count at fractal level

### Other observables (inherit N_U)
- `Physics/MuOverEFinitist.mu_over_e_finitist`
- `Physics/OmegaLambdaFinitist.omega_lambda_finitist`
- `Physics/HiggsMassFinitist.higgs_finitist`
- `Physics/FinitistObservableChain.finitist_observable_chain`
  — 4-observable bundle

## Pisano-CRT framework (number theory)

### 3 recurrence families
- `Math/Cohomology/DyadicThreeFamilyCapstone.three_family_pisano_capstone`
- Pell: 23 primes (3 sub-tight at p=29, 47, 89, 101)
- Pell-proper: 8 primes
- Fibonacci: 8 primes
- Tribonacci: 4 moduli
- Cross-recurrence: `DyadicFibPellRelation.fib_predict_eq_two_pell_predict`

## Hodge involution (Open Problem #5)
- `Math/Cohomology/HodgeInvolutionCapstone.hodge_involution_5strata_capstone`
  — Δ⁴ all 5 strata

## Universal Lens metatheory (Open Problem #6)
- `Meta/UniversalLensTripleCapstone.universal_lens_triple_capstone`
- `Meta/UniversalLensPaddingCapstone.padding_capstone`
  — abstract padding lemma + 4 instances

## Class C atomic catalog (Famous Coincidences)
- `Physics/FamousCoincidences.famous_coincidences_capstone` — Lenz, Koide, r_p, hierarchy
- `Physics/FamousCoincidencesII.class_c_atomic_catalog`
- `Physics/FamousCoincidencesIII.famous_coincidences_III_capstone` — gauge + reps
- `Physics/FamousCoincidencesIV.famous_coincidences_IV_capstone` — exceptional Lie groups
- `Physics/MagicNumbersAtomic.nuclear_magic_atomic_capstone` — 7/7 magic

## Real213 precision artifact closures (F6 doc)

- `Research/Real213CutMulConstConst.cutMul_const_const_forward`
- `Research/Real213CutSumGeneral.cutSum_same/diff_denom_forward`
- `Research/Real213BracketCauchyModulus.dyadic_bracket_cauchy_modulus`
- `Research/Real213PartialSumGeneral.partialSum_const_b_forward`
- `Research/Real213CutMulConstSum.cutMul_const_distrib_forward`

## Substrate / metalogic

- `OS/Atomicity.atomic_iff_five` — d=5 unique
- `OS/PairForcing.pair_forcing` — (2,3) coprime pair unique
- `Research/AxiomMinimality.raw_minimality_capstone` — 4 clauses essential
- `Meta/UniversalLens.universal_lens_capstone` — universal lens existence
- `Meta/SelfRecognising` — R12/R3/R4Codomain hierarchy
- `Meta/BoolLens.boolXorLens_not_homomorphism` — XOR fails R4

## Falsifiability

- `Physics/Generations` — N_gen = 3, no 4th gen
- `Physics/ThetaQCD.theta_QCD_pattern` — θ_QCD < J·α⁴ < bound
- `seed/FALSIFIABILITY.md` — 7 observational falsifiers

## Documentation files

Must-read for new sessions:
- `CLAUDE.md` — project instructions
- `LESSONS_LEARNED.md` — finitist position guardrails
- `HANDOFF.md` — current state
- `CAPSTONE_INDEX.md` — this file
- `seed/AXIOM.md`, `seed/PHILOSOPHY.md`

## Lean library map

```
lean/E213/
  Kernel/    — deep-embedded 213 kernel (101 thms, 0 axiom)
  Firmware/  — Raw axiom layer (a, b, slash, slash_comm)
  OS/        — Atomicity + PairForcing (d=5, (NS,NT)=(3,2))
  Hypervisor/— Lens framework
  Meta/      — Universal Lens, AxiomMinimality, R4Codomain
  Math/      — math (Cohomology, Linalg)
  Physics/   — physics formalization
  Research/  — exploratory proofs
  Infinity/  — limit/compactification
  App/       — applications
  Tactic/    — custom tactics
```

## Key invariants (cross-cutting atomic identities)

  - NS = 3, NT = 2, d = 5, c = 2  (atomic primitives, derived theorems)
  - NS² - 1 = 8  (1/α_3, color confinement)
  - d² - 1 = 24  (SU(5) adjoint)
  - d² = 25  (Gram dim)
  - NS² · d = 45 (SO(10) adj, 3 gens × 15)
  - NS · NT = 6  (Lenz)
  - NS + 1 = d - 1 = 4  (SU(5) face / Dyson)
  - d^(d²) = 5²⁵ = 298023223876953125 (N_universe)
