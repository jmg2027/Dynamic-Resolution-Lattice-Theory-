# CAPSTONE INDEX — 213 master theorems organized

Quick navigation for major Lean capstones.  Updated 2026-05-18 audit
(re-verified each citation against current source).

## Top-level achievements

### Validation Standard satisfied
- `Lib/Physics/Capstones/ValidationStandardOne.validation_standard_capstone`
  — CLAUDE.md #1+#2 explicit, 13 conjuncts, STRICT 0-AXIOM

### Pure atomic closure (strongest)
- `Lib/Physics/Capstones/PureAtomicObservables.pure_atomic_observables_capstone`
  — 17 conjuncts, no N_U dependence, pure rational

## Finitist N_U chain (Standard #1)

### α_em chain
- `Lib/Physics/AlphaEM/Augmented.alpha_em_so10_capstone` — 4 ppm → 15 ppb
- `Lib/Physics/AlphaEM/Augmented.alpha_em_gram_capstone` — 15 ppb → 0.18 ppb
- `Lib/Physics/AlphaEM/Capstone.alpha_em_master_capstone` — 8-conjunct master

### N_resolution identification
- `Lib/Physics/Foundations/NResolutionFromFractal.n_resolution_atomic_decomposition`
- `Lib/Physics/Foundations/NResolutionFractalDepth.n_resolution_self_consistent`
  — L = d² self-referential
- `Lib/Physics/Foundations/FractalLensCardinality.fractal_lens_cardinality_capstone`
  — Lens count at fractal level

### Other observables (using N_resolution as count-Lens readout)
- `Lib/Physics/Mass/MuOverE` — `mu_over_e_simplicial_pattern`
  (the former `MuOverEFinitist` was absorbed here 2026-05-05)
- `Lib/Physics/Cosmology/DarkEnergy.dark_energy_pattern_capstone`
  (former `OmegaLambdaFinitist` absorbed 2026-05-05)
- `Lib/Physics/Higgs/Mass` — `alpha_correction_structure`
  (former `MassFinitist` absorbed 2026-05-05)
- `Lib/Physics/Capstones/FinitistObservableChain.finitist_observable_chain`
  — 4-observable bundle (the surviving aggregator)

### Cross-observable bridge — NS·NT·π⁵ skeleton (2026-05-20)
- `Lib/Physics/Capstones/NSNTPi5Block.ns_nt_pi5_block_capstone`
  — m_p/m_e and 1/α_em(IR) gap as two readings of the same
  NS·NT·π⁵ skeleton (4 PURE theorems)

## Pisano-CRT framework (number theory)

### Per-family capstones (post-DyadicFSM promotion from Cohomology)
- `Lib/Math/DyadicFSM/Pell/Capstone.pell_capstone` — 6-conjunct
  Pell capstone (23 primes, 3 sub-tight at p = 29, 47, 89, 101;
  Pell-proper: 8 primes)
- `Lib/Math/DyadicFSM/Fib/PisanoCapstone.fib_pisano_predict_correct`
  — Fibonacci variant (8 primes)
- `Lib/Math/DyadicFSM/Trib/Capstone.tribonacci_capstone` — Tribonacci
  variant (4 moduli)
- `Lib/Math/DyadicFSM/Trib/CRTCapstone.trib_crt_capstone`,
  `Lib/Math/DyadicFSM/Trib/CRT4Capstone.trib_crt_4_capstone`
  — CRT closures
- Cross-recurrence: `Lib/Math/DyadicFSM/Fib/PellRelation.fib_predict_eq_two_pell_predict`

## Hodge involution (Open Problem #5)
- `Lib/Math/Cohomology/Hodge/InvolutionCapstone.hodge_involution_5strata_capstone`
  — Δ⁴ all 5 strata

## Universal Lens metatheory (Open Problem #6)
- `Lens/Universal/Witnesses/TripleCapstone.universal_lens_triple_capstone`
- `Lens/Universal/Witnesses/PaddingCapstone.padding_capstone`
  — abstract padding lemma + 4 instances
  (moved Meta/UniversalLens → Lens/Universal/Witnesses 2026-05-13)

## Class C atomic catalog (multi-reading magic integers)
- `Lib/Physics/Foundations/AtomicSuperCatalog.super_catalog` —
  consolidated multi-output catalog (absorbs former
  `FamousCoincidences/{Atomic, MultiReading, GaugeGroup, ExceptionalLie}`
  cluster 2026-05-05; further moved
  `AtomicCorrespondences/AtomicSuperCatalog` → `Foundations/`).
  Covers integers 6, 8, 12, 16, 24, 25, 27, 32, 45, 60, 120, 192,
  240, 248 with multi-reading atomic decompositions.
- Physics-named coincidences live in their natural topical files:
  - `Lib/Physics/Hadron/ProtonElectronRatio.six_atomic_dual` (Lenz)
  - `Lib/Physics/Foundations/KoideFormula.koide_atomic` (Koide)
  - `Lib/Physics/Hadron/ProtonMass.r_p_v2_atomic` (proton radius)
  - `Lib/Physics/Mass/HierarchyTowers.hierarchy_from_cardinality`
- `Lib/Physics/Nuclear/MagicNumbersAtomic.nuclear_magic_atomic_capstone` — 7/7 magic

## Real213 precision artifact closures (F6 doc)

- `Lib/Math/Real213/Mul/CutMulConstConst.cutMul_const_const_forward`
- `Lib/Math/Real213/Sum/CutSumGeneral.cutSum_same_denom_forward`
- `Lib/Math/Real213/Sum/CutSumGeneral.cutSum_diff_denom_forward`
- `Lib/Math/Analysis/BracketCauchyModulus.dyadic_bracket_cauchy_modulus`

## Substrate / metalogic

- `Theory/Atomicity/Five.atomic_iff_five` — d=5 unique
- `Theory/Atomicity/PairForcing.pair_forcing` — (2,3) coprime pair unique
- `Theory/Raw/ParenthesizationDistinct.parenthesisation_distinct`
  — `(a/b)/z ≠ a/(b/z)` for concrete `z`; no universal `slash`
  associativity (added 2026-05-18)
- `Theory/Raw/ParenthesizationDistinct.same_leaves_distinct_parenthesisation`
  — both parenthesisations have leaves count = 5, yet are distinct
  Raws.  The concrete "projection many-to-oneness" witness:
  `Lens.leaves.view` collapses different Raws to the same `Nat`
  (added 2026-05-18)
- `Theory/Raw/Congruence` + `Lens/Congruence` — `Eqv (gens) ↔
  L.equiv` biconditional for any lens (added 2026-05-18);
  `Lens.leaves_view_surjective_on_ge_one` realises every `n ≥ 1`
  as the leaves count of `numeral (n - 1)` — the rigorous form of
  "ℕ₊ = Range(Lens.leaves.view)"
- `Theory/Raw/Congruence.Eqv.weaken` — `Eqv` is monotone in its
  generator (added 2026-05-18); `Eqv.of_eq`, `Eqv.empty_iff_eq`
  + `Lens.Eqv_monotone_in_lens` complete the basic `Eqv` API
- `Lens/Number/Nat213/ChartGeneral.chartChain_value` —
  chart-invariance over any `(r₀, r')` with `r₀ ≠ r'` (added
  2026-05-18; explicit form of axiom §9.1's chart-relativity)
- `Lens/Number/Nat213/ChartGeneral.chartChain_injective` —
  the chain map `n ↦ chartChain r₀ r' h n` is injective in `n`
  (any chart provides a bijective ℕ → Range labelling; added
  2026-05-18 via `value_pos` + `mul_left_cancel_pos`)
- `Lens/SyntacticInternalization.parseTree_printTree` —
  Polish-prefix universal round-trip
  `∀ t, parseTree (printTree t) = some t` (added 2026-05-18)
- `Lens/SyntacticInternalization.printTree_parseTree` — reverse
  direction: `parseTree gs = some t → printTree t = gs`
  (lossless parser; added 2026-05-18 L4 closure)
- `Lens/SyntacticInternalization.printTree_injective` —
  `printTree t₁ = printTree t₂ → t₁ = t₂` (closes the bijection
  between `Tree` and `Range(printTree)`)
- `Meta/AxiomMinimalityCapstone.raw_minimality_capstone` — 4 clauses essential
- `Lens/Universal/QuotLens.universalLens` — universal lens existence
  (`IsUniversal` predicate + `idLens_is_universal` are in
  `Lens/Universal/Witnesses/Core`)
- `Meta/SelfRecognising` — CommBinary/NonVanishing/Conjugation Codomain hierarchy
- `Lens/Instances/Bool.boolXorLens_not_homomorphism` — XOR fails R4

## Falsifiability

- `Lib/Physics/Simplex/Generations.drlt_no_4th_gen_falsifier` — N_gen = 3, no 4th gen
- `Lib/Physics/Couplings/ThetaQCD.theta_QCD_pattern` — θ_QCD < J·α⁴ < bound
- `seed/AXIOM/08_falsifiability.md` — 7 observational falsifiers

## Documentation files

Must-read for new sessions:
- `CLAUDE.md` — project instructions
- `LESSONS_LEARNED.md` — finitist position guardrails
- `HANDOFF.md` — current state
- `CAPSTONE_INDEX.md` — this file
- `seed/AXIOM/`, `seed/AXIOM/01_residue.md`

## Lean library map

```
lean/E213/
  Term/      — Raw 의 구현체 (Tree substrate + Bool comparators
               + Sound bridges; 17 files, ★ literally 0 axiom)
  Theory/    — Raw axiom (a, b, slash, slash_comm) + Atomicity
               (d=5, (NS,NT)=(3,2) forced uniqueness) + CDDouble
               + Congruence + ParenthesizationDistinct
               (24 files post-2026-05-18 cleanup; Bool213 /
               Nat213 / RawCut migrated to Lens 2026-05-14)
  Lens/      — Lens framework (catamorphism Raw → α) + sub-clusters
               (Algebra, AxiomLenses, Bool213, Cardinality, Compose,
                Congruence, Instances, Lattice, Number,
                Properties, SyntacticInternalization, Universal)
               (144 files)
  Lib/Math/  — math (Cohomology, Linalg, Real213, CayleyDickson,
               Probability, …; 727 files in 42 sub-clusters)
  Lib/Physics/— physics formalization (165 files in 17 sub-clusters)
  Meta/      — ring-independent Lean bridge (Tactic, SelfRecognising,
               AxiomMinimality, LensInternality, List213, …;
               37 files)
```

## Key invariants (cross-cutting atomic identities)

  - NS = 3, NT = 2, d = 5, c = 2  (atomic primitives, derived theorems)
  - NS² - 1 = 8  (1/α_3, color confinement)
  - d² - 1 = 24  (SU(5) adjoint)
  - d² = 25  (Gram dim)
  - NS² · d = 45 (SO(10) adj, 3 gens × 15)
  - NS · NT = 6  (Lenz)
  - NS + 1 = d - 1 = 4  (SU(5) face / Dyson)
  - d^(d²) = 5²⁵ = 298023223876953125 (N_resolution)

## 2026-05-20 — Deep philosophical revision pass additions

New capstones from the 14-agent audit + revision pass:

### §9.3 + §9.5 flat-ontology realisation (Lens)

  - `Lens/FlatOntology.flatOntology` — objects, types,
    relations, functions, Lens as decidable predicates on
    Raw^n (12 PURE).
  - `Lens/PredicateSelfEncoding.predicate_self_encoding_closure` —
    predicates back to Raw via positional Gödel numbering
    (7 PURE, closing the §9.3 loop).
  - `Lens/RawTopology.k_infty_at_raw_bundle` — K_∞ ≡ point at
    raw level (constLens bookend) plus discrete bookend (idLens
    kernel = equality) plus two-bookend bracket — §9.5 witness,
    7 PURE.  (Previously split between `UndifferentiatedRaw` and
    `RawTopology`; merged 2026-05-20 to remove triple-redundant
    reformulations.)

### §1.3 three-direction uniqueness bundle (Meta)

  - `Meta/ThreeDirectionUniqueness.three_direction_uniqueness` —
    single statement bundling Below (4-clause minimality) +
    Sideways (universal-Lens factoring) + Above (Atomic ↔ five).

### §3.4 + §8.7 Möbius frozen + dynamic (Lib/Math)

  - `Lib/Math/Mobius213.mobius_213_char_poly_at_trace` — φ²,
    1/φ² eigenvalues encoded at integer level.
  - `Lib/Math/Mobius213.mobius_213_pell_unit_invariant_layer{0..4}` —
    `num_n · den_{n+1} − num_{n+1} · den_n = -1` across
    convergent layers, witnessing det = 1 (same algebraic
    content, frozen + dynamic readings).

### §4.5 forcing chain (Meta)

  - `Meta/AxiomMinimalityCapstone.raw_forcing_chain_unified` —
    positive complement to `raw_minimality_capstone`; records
    the 1 → 2 → 3 → 4 structural forcing.

### §8.8 Universal P^n ↔ Fibonacci (Lib/Math/Mobius213/Px)

  - `Px.PnFibonacciUniversal.det_pn_universal` — det(P^n) = 1 ∀n
    (Fibonacci Cassini at even indices, PURE Nat ring).
  - `Px.CassiniUniversal.cassini_universal` — L(n)·L(n+2) = L(n+1)²+5
    ∀n (Nat-additive reformulation).
  - `Px.QFibIdentity.Q00_eq_fib` — **NEW**: Q00 n = fib(2n+1) ∀n.
  - `Px.QFibIdentity.Q01_eq_fib` — **NEW**: Q01 n = fib(2n) ∀n.
  - `Px.QFibIdentity.pn_fibonacci_universal` — **NEW**: full P^n entry
    formula ∀n: `P^n = [[fib(2n+1), fib(2n)], [fib(2n), fib(2n-1)]]`.

All 29 new symbols verified PURE via `tools/scan_axioms.py`.
