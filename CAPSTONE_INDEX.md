# CAPSTONE INDEX — 213 master theorems organized

Quick navigation for major Lean capstones.  Updated 2026-05-01.

## Top-level achievements

### Validation Standard satisfied (root)
- `Physics/Capstones/ValidationStandardOne.validation_standard_capstone`
  — CLAUDE.md #1+#2 explicit, 13 conjuncts, STRICT 0-AXIOM

### Pure atomic closure (strongest)
- `Physics/Capstones/PureAtomicObservables.pure_atomic_observables_capstone`
  — 17 conjuncts, no N_U dependence, pure rational

## Finitist N_U chain (Standard #1)

### α_em chain
- `Physics/AlphaEM/SO10.alpha_em_so10_capstone` — 4 ppm → 15 ppb
- `Physics/AlphaEM/GramSelfEnergy.alpha_em_gram_capstone` — 15 ppb → 0.18 ppb
- `Physics/AlphaEM/MasterCapstone.alpha_em_master_capstone` — 8-conjunct master

### N_universe identification
- `Physics/Foundations/NUniverseFromFractal.n_universe_atomic_decomposition`
- `Physics/Foundations/NUniverseFractalDepth.n_universe_self_consistent`
  — L = d² self-referential
- `Physics/Foundations/FractalLensCardinality.fractal_lens_cardinality_capstone`
  — Lens count at fractal level

### Other observables (inherit N_U)
- `Physics/Mass/MuOverEFinitist.mu_over_e_finitist`
- `Physics/Cosmology/OmegaLambdaFinitist.omega_lambda_finitist`
- `Physics/Higgs/MassFinitist.higgs_finitist`
- `Physics/Capstones/FinitistObservableChain.finitist_observable_chain`
  — 4-observable bundle

## Pisano-CRT framework (number theory)

### 3 recurrence families
- `Math/Cohomology/Dyadic/ThreeFamilyCapstone.three_family_pisano_capstone`
- Pell: 23 primes (3 sub-tight at p=29, 47, 89, 101)
- Pell-proper: 8 primes
- Fibonacci: 8 primes
- Tribonacci: 4 moduli
- Cross-recurrence: `Math/Cohomology/Dyadic/Fib/PellRelation.fib_predict_eq_two_pell_predict`

## Hodge involution (Open Problem #5)
- `Math/Cohomology/HodgeInvolutionCapstone.hodge_involution_5strata_capstone`
  — Δ⁴ all 5 strata

## Universal Lens metatheory (Open Problem #6)
- `Meta/UniversalLens/TripleCapstone.universal_lens_triple_capstone`
- `Meta/UniversalLens/PaddingCapstone.padding_capstone`
  — abstract padding lemma + 4 instances

## Class C atomic catalog (Famous Coincidences)
- `Physics/FamousCoincidences/Atomic.famous_coincidences_capstone` — Lenz, Koide, r_p, hierarchy
- `Physics/FamousCoincidences/MultiReading.class_c_atomic_catalog`
- `Physics/FamousCoincidences/GaugeGroup.famous_coincidences_III_capstone` — gauge + reps
- `Physics/FamousCoincidences/ExceptionalLie.famous_coincidences_IV_capstone` — exceptional Lie groups
- `Physics/Nuclear/MagicNumbersAtomic.nuclear_magic_atomic_capstone` — 7/7 magic

## Real213 precision artifact closures (F6 doc)

- `Research/Real213/CutMulConstConst.cutMul_const_const_forward`
- `Research/Real213/CutSumGeneral.cutSum_same/diff_denom_forward`
- `Research/Real213/BracketCauchyModulus.dyadic_bracket_cauchy_modulus`
- `Research/Real213/PartialSumGeneral.partialSum_const_b_forward`
- `Research/Real213/CutMulConstSum.cutMul_const_distrib_forward`

## Substrate / metalogic

- `Firmware/Atomicity/Five.atomic_iff_five` — d=5 unique
- `Firmware/Atomicity/PairForcing.pair_forcing` — (2,3) coprime pair unique
- `Research/AxiomMinimalityCapstone.raw_minimality_capstone` — 4 clauses essential
- `Meta/UniversalLens/Core.universal_lens_capstone` — universal lens existence
- `Meta/SelfRecognising` — R12/R3/R4Codomain hierarchy
- `Hypervisor/Lens/Instances/Bool.boolXorLens_not_homomorphism` — XOR fails R4

## Falsifiability

- `Physics/Simplex/Generations` — N_gen = 3, no 4th gen
- `Physics/Couplings/ThetaQCD.theta_QCD_pattern` — θ_QCD < J·α⁴ < bound
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
  Firmware/  — Raw axiom (a, b, slash, slash_comm) +
               Atomicity/ (d=5, (NS,NT)=(3,2) forced uniqueness)
  Hypervisor/— Lens framework + Lens/{Instances, Characterisation}/
  Meta/      — UniversalLens, SelfRecognising R1-R4, BitPatternUniqueness
  Math/      — math (Cohomology, Linalg, Pigeonhole)
  Physics/   — physics formalization (18 sub-clusters)
  Research/  — exploratory proofs (17 sub-clusters)
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
