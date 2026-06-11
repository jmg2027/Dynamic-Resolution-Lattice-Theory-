# research-notes/frontiers/ — the open-frontier board

The **live research agenda**: the open problems / conjectures / unproven
directions that are *not yet closed*.  This is the open side of the
research cycle —

```
  frontier note here  ──(work)──▶  Lean ∅-axiom closure  ──(promote)──▶  theory/ chapter or essay
        ▲                                                                          │
        └──────────────── archive the source note (record of the path) ◀──────────┘
```

When a frontier closes (PURE + categorically complete per
`theory/PROMOTION_CRITERIA.md`), promote it to `theory/` and move its
notes to `research-notes/archive/<topic>/`.  Top-level `research-notes/`
keeps only the boot-sequence anchors; everything in motion lives here,
grouped by topic; everything closed lives in `archive/`.

Tier-1 volatile (CLAUDE.md "no session-number in long-lived names" does
not apply — `G##` chronological prefixes are fine in scratch).

---

## π continued-fraction non-holonomicity  (`pi_nonholonomicity/`)

**Core open problem (classical):** is the partial-quotient sequence of π
non-holonomic (satisfies no linear recurrence with polynomial
coefficients)?  Strictly above "π non-Hurwitzian" (a sequence can be
non-Hurwitzian yet holonomic, as `2ⁿ` shows).

- `G170_pi_cf_nonholonomicity` — the marathon scratchpad: what is provable
  ∅-axiom (the `(n!)ⁿ` and powers-of-2-indicator non-holonomic witnesses)
  vs. what stays classical-open for π itself.
- `G173_pi_cf_boundedness_frontier` — the *boundedness* frontier: where the
  difficulty of π actually lives (bounded ⇒ elementary non-holonomicity via
  Lagrange; π's p.q. are expected unbounded, so that route is unavailable).
- `G175_fgs_boundary_and_mod2_obstruction` — the constructive boundary: FGS
  asymptotics have no ∅-axiom shadow, the mod-2 (Garrabrant–Pak) obstruction
  does; concrete next targets.
- `G184_gp_mod2_subsumed` — the GP mod-2 obstruction is subsumed (for its
  witnesses) by the zero-run + two-continuation criteria; what remains
  genuinely heavy.
- `G174_pi_residue_continuous_symmetry` — conjectural: π as the
  continuous-symmetry image of the residue (φ/π two-faces).  Conceptual, not
  a theorem; flags one category error to avoid.
- `forall_form_characterization` — ★ the originator's **∀-form**: π as the
  universal escape-residue of the modulus family ("whatever modulus you bring,
  what remains"), debate-audited (3 rounds, critic web-verified).  Verdict:
  characterization + correctly-typed program, not a definition — quantified
  form = the measure hypothesis (`PiHalfMeasure`), sole honest instantiation
  **Mahler 1953 `(C,s) = (1,42)`** (only published explicit measure for π);
  place/character/number separation (solenoid theorem / forced `e^{±2πix}` /
  series anchor); the algebraic→transcendental wall discontinuity; genericity
  tension (μ(π) = 2 conjectured — specialness lives in effectivity).  Build
  candidate: uniform period-spectrum capstone (`M^n = I ⟹ ord ∈ {1,2,3,4,6}`,
  ~250 lines).

Closure record (the proven side of this arc):
`theory/math/analysis/{cf_holonomicity_hierarchy,phi_pi_poles}.md`.

## Markov / Lagrange spectrum  (`markov_lagrange/`)

**Core open problem:** the Markov uniqueness conjecture (Frobenius 1913) —
each Markov number determines a unique triple.  **Current state (`G204`):** the
prime-power-neighbour families are ∅-axiom *closed* (`pᵏ`, `2·pᵏ`, and `3c±2`
a prime power — Zhang's modulus-shift criterion); the residual is the
class-number core (composite `c` with both `3c±2` composite, smallest `1325`).

- `G204_post_zhang_residual` — **standing record after the prime-power families
  closed**: the closure table (`markov_prime_pow_unique`, `markov_two_prime_pow_unique`,
  `markov_max_unique_via_3c_pm2`, `markovMaxUnique_985`) + the sharpened residual
  (class-number / fundamental-unit core) + the REFRAME tool and its limit.
- `G173_markov_uniqueness` — the ∅-axiom arithmetic spine (neighbor
  congruence, √(−1) encoding, Button prime-power closure) + the conjecture
  slate reducing composite uniqueness to one realisability hypothesis `H`.
- `G172_lagrange_threads` — three approximation-spectrum threads
  (Stern-Brocot, φ/π extremes, Hurwitz cosines).
- `G174_markov_newton_synthesis` — idea-level graft of Markov uniqueness onto
  the Newton / Casoratian / FSM frameworks (Myhill–Nerode reading of the crux).
- `G189_geodesic_lens_markov_frontier` — the geodesic-Lens view: where
  stable-norm / Christoffel sits relative to the mediant engine.
- `G190_foundation_breakthrough_backlog` — a map of the Raw/Lens corpus and
  where the Markov `H` kernel sits in the foundation's breakthrough backlog.
- `G191_continuant_aigner_program` — the continuant / Aigner program: where
  modern Markov theory meets the repo, and what it can(not) close (the
  ranked-next attack on `H`; `Real213/Continuant.lean` tool built).
- `G192_markov_kernel_raw_lens_native` — the kernel in Raw/Lens-native terms:
  where the geodesic engine reaches and where it structurally stops.
- `G193_axioms_against_markov_kernel` — the 213 axiom corpus read against the
  Markov kernel: a standing attack map for `H`.
- `G194_forced_fixed_point_attack` — the forced-fixed-point attack on `H` (and
  why it returns to the conjecture's difficulty).
- `G195_cohomology_selection_probe` — the cohomological δ angle on the kernel: a
  real space-identification, a refuted selection.
- `G196_H_compiled_to_the_isa` — `H` compiled to the proof-ISA; the one missing
  composition named (a cross-word continuant-trace `SEPARATE`).
- `G197_isa_localization_terminal` — ★ **terminal finding**: the ISA compilation
  has **maximally localized `H`** to one irreducible instruction-residue (the
  uniform cross-word continuant-trace `SEPARATE`), everything around it ∅-axiom,
  finite instances `decide`-verified (`markovNum_injective_pathsUpTo_4`).  Pointing
  at the uniform residue **is Frobenius (1913) itself — not a bounded step**.
- `G198_action_options_ABC` — post-localization options (A loop/µ-ν certification
  via `slashNu_final`, B compilation catalog, C …); each circles back to the full
  difficulty.
- `G199_compilation_catalog_lift_archetypes` — the finite→uniform lift archetypes
  (the compilation-catalog methodology generalised).
- `G200_action_A_distance1_crossline_separate` — action A executed: the
  **distance-1 cross-line `SEPARATE`** closed ∅-axiom (`markovNum_children_ne`,
  `SternBrocotMarkov` §35) — every node's two children carry distinct Markov
  numbers; the size route localized as exhausted.
- `G201_action_b_even_markov_family` — action (b): the **even `2·pᵏ` infinite
  uniqueness family** closed ∅-axiom (`markov_two_prime_pow_unique`; first
  instance `markovMaxUnique_34`).
- `G202_zhang_3c_pm2_roadmap` — expert-agent attack on the open kernel:
  **Zhang's `3c±2` modulus-shift criterion** — verified, formalization-ready
  roadmap to the composite/even families, plus a sharp delineation of where
  elementary methods provably stop.
- `G203_reframe_archetype_modulus_shift` — the `3c±2` modulus shift compiled to
  all four layers (Raw / Lens / proof-ISA / residue): the **REFRAME** lift
  archetype (A4) extracted from `markov_max_unique_via_3c_minus_2`.

Closure record: `theory/math/analysis/{markov_uniqueness,markov_spectrum}.md`.
**Status of `H`**: maximally localized (terminal, `G197`) — the open residue *is*
the Frobenius conjecture; the Lean scaffold + finite instances are ∅-axiom.

## Spiral-axis / modular-tower classification  (`spiral_axis/`)

**Core open problem:** a classification of reals finer than
algebraic/transcendental, by 213-native count-coordinates (layer = divergence
depth; axis = unit-group order `{2,4,6}`), and its tower extension.

- `G169_spiral_coordinate_classification` — the classification itself
  (layer × axis), what is ∅-axiom vs conjectured.
- `G171_modular_tower_axes` — the axis/lattice/shape/constant tower
  (SL(2)→PSL→SL(3); e→π→ζ(3)); honest split of proven vs speculative rows.
- `G185_spiral_axis_deep_research` — the two CM points and the honest unifier
  for `{2,4,6}=2·{1,2,3}` ↔ Cassini sign; ranked conjecture agenda (A5…).

Closure record: `theory/math/analysis/spiral_coordinate_classification.md`.
`G181_atomic_spiral_adic` (the variable-base adic / carry = the residue unit) is
**closed**, built as `Theory/Raw/{Odometer,OdometerValue}` + `Real213/ZeckendorfCarry`,
narrated in `theory/essays/foundations/the_residue_unit_odometer.md` +
`theory/math/algebra/phi_self_similarity.md` §3.7.

## Real-completeness / intensional completability  (`completability/`)

**Core open problem:** completability as an intensional invariant — the
presentation/real split, and when a rate-free presentation (π) completes.

- `G169_intensional_completability_conjectures` — the presentation/real split
  + supporting ∅-axiom lemmas + the conjectures it opens.
- `G149_analysis_continuum_space_insights` — the analysis/continuum/space
  insight map feeding the completability and GRA programmes.

Closure record: `theory/math/numbersystems/{completeness_relocated,completeness_without_completeness}.md`
+ `theory/math/analysis/{holonomic_modulus,tower_native_completeness,refined_completability_engine}.md`.

## Sequence depth / multiplicative machinery  (`sequence_depth/`)

**Core open problem:** the multiplicative twin of the additive
finite-depth algebra (Hadamard product, Casoratian rank, holonomic `ℚ(n)`-orbit).

- `G188_depth_order_duality` — depth/order duality as the founding invert-twin
  at the sequence scale.
- `G188_multiplicative_conv_design` — `mconv` (multiplicative twin of `conv`):
  the power-sum/Newton route, with an honest ∅-axiom feasibility verdict.
- `multiplicative_carry_residue` — the digit-scale mirror: p-adic `×` is native corecursive
  (`mul_corecursive`) but not finite-state (`mulRaw_unbounded`/`mulCarry_unbounded`, dual of
  `add_carry_le_one`); the unbounded carry IS a νF inhabitant (`carry_is_nu_escape`) — core closed,
  only the Lens-reading refinement soft-open.

Closure record: `theory/math/analysis/{divergence_depth_characterization,cfinite_orbit_dimension}.md`.

## Standalone frontiers (root of `frontiers/`)

- `slots_crossdomain` — **the slot programme ↔ the graded-ladder / π
  arc** (merge note): one crystallographic restriction at two scales
  (unit-group phase budget = finite matrix orders, both `{1,2,3,4,6}`
  via `φ(n) ≤ 2`); escape-from-every-X theorems as one form (schedules
  / slot grammars / moduli); modulus degree = certificate depth =
  answer-axes (fold-back dimension), three scales of one
  Lens-property.  Three bridge theorems named, all open.

- `numbersystem_square` — **the number-system square**: ℕ→ℤ→ℚ vs
  ℕ→ℚ₊→ℚ, two Lenses (difference, ratio) applied in two orders;
  distributivity as the commutation law (the reason both routes
  converge to one ℚ), the judgment formulas (sandwich, coprimality) as
  membership detectors across levels.  Open: the ℚ₊→ℚ leg, the
  square-commutes theorem, the frames essay after closure.

- `slot_tower_debate` — **two-round panel verdicts on the slot-tower
  arc**: thesis/mechanism/debt triage (atom-(in)distinguishability /
  the count-rig `iter_add`+`iter_mul` / `vp_separation`); the ^-wall is
  two independent proof-facts until the `exp`-iso bridge closes; fold
  criterion scoped (ℚ-exponents, `a,b≥2`; ⟹ provable now, ⟸ IS
  separation); **genesis verdicts RETRACTED** — the panel's "binary
  `slash` genesis / Raw bifurcates / *first* distinguishing" read the
  Lean encoding as Raw ontology (the §6.1/§6.2 failure) and misquoted
  "방법이 하나" (method-uniqueness) as "pick one"; Raw neither splits
  nor has a first, and the originator's real point is method-uniqueness
  of *measuring* (append = the gathering-Lens) from inexhaustibility +
  numberlessness; 12-item merged brick agenda (keystone `vp_separation`
  now CLOSED, `Meta/Nat/VpSeparation.lean`; the fold criterion and the
  order-loss theorem also closed).

- `slot_tower_crossdomain` — **slot tower ↔ main** (2026-06-11 merge): four
  open bridges.  (1) equality is a certificate with a shape (weld Padé-flip
  ↔ `FoldCriterion.pow_eq_pow_iff_vp`); (2) order ⟺ no-wrap, exact duals
  both proved (`Int213.OrderMul` ↔ `NoOrderModP.no_wrapping_order`); (3) the
  exp/log boundary, tame vs wild (LambertWeld `exp(2/q)` ↔ the `^`-wall
  `fold_iff_collinear`); (4) the substrate's shape, metric vs topological
  (`Shape213`/`GridReadout213` ↔ discrete Ricci/curvature).  Single-schema
  Lean statements not yet written.

- `modulus_degree_crossdomain` — **the modulus-degree branch ↔ merged main**: (1)
  modulus degree IS certificate depth one layer up (proof-layer SOS fold-depth ↔
  completeness-layer receipt count; both Lens-properties of the pointing, object
  invariant); (2) `reschedule_limit_eq` is "the stage is of the run" at the real
  layer — the modulus is of the run, the real is the run-invariant, `powSched_mono`
  orders the runs.  Open: the four-scale cover-non-surjection schema stated once.
- `modulus_degree_ladder` — **grading "completes" beyond the binary**.  Closed:
  the algebraic pillar at degrees 2 (φ form cut) and 3 (`CubeRootTwoCut`, 31
  PURE: side-decision = `ε·k³ < d³`, total modulus `N = 3k+5`, fold lands on
  the frozen form cut) — algebraic degree enters as the probe exponent `k^s`,
  presentation-robust, vs the transcendental-only `W`-vs-`d` race; and the
  **graded rate generator** (rung 1): the margin telescope parametrized by a
  probe schedule (`HtelS`/`DominatesS`, `RateModulus`/`RateStratification`),
  `ρ = rootFloor s` ⟹ `N = k^s + 1`, strictness witnessed by `sepDen`
  (root-2-rescued, identity-broken at layer 4); and the **conditional
  measure-modulus schema** (rung 2): the bracket-exclusion engine
  (`BracketModulus`, `N = B k + 2`) + the proved-decreasing Wallis upper
  companion `U_n = W_n·(2n+2)/(2n+1)` give **π conditionally degree-`s`**
  (`PiMeasureModulus`: `PiHalfMeasure C s` ⟹ π modulus `C·(2k)^s + 2`).
  Schedule comparison law closed (`dominatesS_schedule_mono`: the gap law is
  the exact extra condition; pointwise the ladder is not a chain).  ζ(3)
  engine end closed (`aperyOrbit_geom` 28-growth + `zeta3_reduced_conditional`).
  Open: an actual effective `(C,s)` for π, ζ(3)'s I1/I2 (Apéry integrality +
  Hanson lcm), the two-real separation modulus, degree-4+ form cuts, `dyUp`
  tightness.
- `zeta3_free_modulus` — **ζ(3): built fold → free total modulus**.  The fold is
  closed (`Real213/Zeta3Cut`, 35 PURE: exact ℕ Apéry recurrence + closed-form
  Casoratian `6·(m!)⁶` + `AbCutSeq` + bracket `601/500 < ζ(3) ≤ 1203/1000`), and
  the built presentation is *proved* rate-free (`zeta3_presentation_overtakes`,
  overtake at layer 9).  Open: the e-grade upgrade — the reduced presentation
  (`2·lcm³·bₙ`) is rate-carrying but needs the two classical Apéry arithmetic
  inputs (reduced-numerator integrality; `lcm(1..n) < 3ⁿ`), then
  `rate_total_modulus` gives `zeta3HolonomicReal` unconditionally.
- **async point–line system ≅ Raw** — CLOSED ∅-axiom (full 8-item agenda,
  74 PURE) and promoted → `theory/math/foundations/async_growth.md`
  (origin: `seed/ORIGIN_RAW.md`; note archived at
  `archive/async_pointline_raw.md`).  Cross-domain bridges to main's
  curvature / LTE / certificate-depth arcs: `async_growth_crossdomain.md`
  (orbit-LTE law, Hasse-diagram curvature, depth-0 squeeze certificate).
  *Open seeds* →
  `async_growth_seeds.md`: exact-membership converse of reachability,
  fused step-3 swap-class census, uniform dagSize bounds, the
  axes-of-growth definition.
- `G35_chiral_cup_ring_catalog` — **the 213-Algebra field catalog** (17 domains):
  the field-level synthesis board, broader than any single `theory/` chapter;
  §0.5 tracks per-conjecture (C1–C6) closure status + promoted chapters.  Active
  scratch — Lean docstrings cite its §C## conjecture labels
  (`research-notes/frontiers/G35`).
- `inequalities_positivity_fold_crossdomain` — **the curvature arc ↔ the proof-ISA arc**:
  A7 POSITIVITY's 2-D Cauchy–Schwarz (`cauchy_schwarz_2d`, depth-0 Lagrange square) and the
  curvature module's n-dim power-mean Cauchy–Schwarz (`cauchy_schwarz_gridZ`, per-rung SOS
  folded along the `gridSumZ` induction) are one instruction at two certificate depths; the
  `K_{a,b}` wide/narrow regime split (`kab_cd_wide`/`kab_cd_narrow`) is literally certificate
  depth.  Open: the "inequality = POSITIVITY ∘ LOOP" compilation theorem (buildable first
  brick: the pair-sum Lagrange identity `n·Σa² − (Σa)² = Σ_{i<j}(a_i−a_j)²`), and the
  evidence it gives on G205's POSITIVITY-vs-GAP question.
- `curvature_spectrum_crossdomain` — **the discrete-curvature / spectrum branch ↔ merged
  main** (rich-flow-open-frontier marathon).  Three bridges where this branch's curvature
  + Lichnerowicz spectral work touches main's `(ℤ/p)*`-cyclic / character arc: (1) the `K_p`
  Laplacian spectrum `{0,p}` (`km_eigenvalue`/`km_meanzero_eigen`) IS the **additive**-character
  spectrum of `ℤ/p`, dual to main's **multiplicative** Legendre character — characters of the
  cyclic group as eigen-data, two ways; (2) the central lattice `K_{3,2}` carries both a golden
  (`5 = NS+NT`) and a curvature (`CD(3/2)` / Forman `−1`) signature, meeting at `a+b = 5`;
  (3) "structure forces the invariant" — Lichnerowicz `CD(K) ⟹ λ₁ ≥ K` parallels cyclicity
  forcing the quadratic character.  Bridge 1 buildable (the `m=p` instantiation); 2–3 conceptual.
- `zolotarev_crossdomain` — **the Zolotarev / permutation-sign branch ↔ merged main**
  (converse-psign marathon).  Four bridges where this branch's closed Zolotarev
  (`psign σ_a = (a/p)`, all primes) + `InversionsAppend` combinatorics touch main's arcs:
  (1) `σ_a` is the finite-state side of the `×unit`/`×p` finite-state-vs-escape split —
  `(a/p)` is the Z/2 invariant the finite pointing carries and the νF escape lacks;
  (2) Zolotarev `psign σ_a = det(permMatrix) = (a/p)` and main's companion-determinant sign
  `altSign(k−1) = psign(shift cycle)` are two closed instances of one "three readouts" schema
  (shared engine `det_permMatrix`); buildable `psign(cyclicShift n) = altSign(n−1)`;
  (3) `crossInv` antisymmetry (off-diagonal pairs cancel mod 2) ↔ det's repeated-row vanishing;
  (4) ★ `psign σ_{−1} = (−1/p) = +1 ⟺ p≡1 mod4 ⟺ i∈ℤ/p` ties the order-2 negation-permutation
  sign to main's order-4 spiral-axis point `ℤ[i]^×=C₄`.
- `selfref_matrix_crossdomain` — **the self-reference matrix `M=[[2,1],[1,1]]` as the common
  root** (apex ↔ Casoratian ↔ axis).  Five connections: (1) the CKM factorises by discriminant —
  modulus on `ℚ(√5)` (+5, golden eigenvalue), phase on `ℚ(i)` (−4, Hodge `⋆`); (2) `det=1`
  unimodularity is the one shared engine (apex reciprocity ↔ `det(AB)=det A·det B` ↔ CKM unitarity
  ↔ Legendre); (3) "modulus = de-signed square" is the same Bool/difference-Lens as the Casoratian/
  Cassini sign; (4) `M` is the companion matrix of `x²−3x+1`, so the fourth-readout companion-sign
  machinery applies to the apex itself; (5) `H*(Δ⁴)` shared by `1/α_em` and the CP phase.  Buildable:
  unimodularity note, companion-cycle reading of the apex, the two eigen-fields of `d=5`.  (The
  `casoratian_axis_cp_crossdomain` note both links closed — `GaussianHodgeBridge` morphism +
  `CasoratianPermSign` sign-bridge — and is archived.)
- `one_carrier_crossdomain` — **the one-carrier branch ↔ merged main** (p-ary-spine marathon).
  (1) "Unit result, non-finite-state generation" at two scales: `(-1)²=1` with unbounded carry
  (`mulCarry_unbounded`/`carry_is_nu_escape`, branch) = Casoratian `q=−1` with no finite holonomic
  depth (`cas_neg_unit_no_finite_depth`/`DetSpectrumPoles`, main) — finite-state is of the *pointing*,
  not the value, on ring-op and sequence scales.  (2) Multiplication's unit/non-unit split IS the
  finite-state/escape split: `× unit` = a finite permutation with a sign (Zolotarev `mulPermMod`,
  main) vs `× p` = the valuation escape (`mulBase_eq_mul_pElem`, branch).  Open bridges noted.
- `fibonacci_golden_prime_crossdomain` — **the Fibonacci 5-adic branch ↔ main's CKM
  CP-phase / Legendre arc**.  The prime `5` is the shared hinge: main takes the *value*
  `φ ∈ ℚ(√5)` (golden modulus `R_u=1/φ²`), the branch the *5-adic valuation* of the Fibonacci
  recurrence (rank `α(5)=5`, `ν₅(F_n)=ν₅(n)`) at the *ramified* prime of the same `ℚ(√5)`.
  Proven shared objects: the Cassini unit `det=±1 = det P = NS−NT = 1` (already cited from
  `OrbitDimension` to `PnFibonacciUniversal`), and the binary sign axis (`ε=(−1)ᵐ` = the
  `psign`/Legendre/inversion read of the permutation-three-readouts).  **CLOSED**: the general-`p`
  rank law `α(p) ∣ p − (5/p)` from the Legendre character (`DyadicFSM/RankApparition.lean`); the
  shared-`ℚ(√5)` morphism tying `cp_phase` ↔ `fibonacci_5adic_valuation` (`x↦−x` between the Binet
  `x²−x−1` and the Gaussian-period `x²+x−1`, `NumberTheory/GoldenFieldBridge.lean`).  **Open**: the
  higher-valuation `νₚ(F_n)` rungs for general `p` (the `p`-tupling analogue of the quintupling
  identity, beyond the entry point), and insight 1 (value-vs-valuation as a conceptual hinge).
- `cp_crossdomain_insights` — **CP-phase cohomology ↔ main's sign/QR/cyclotomic
  campaigns** (merge marathon). Four candidate bridges where the two branches
  share one object: (1) the inversion sign is one object — `det(permMatrix)=psign`
  (main) = the signed Hodge cup wedge sign `(−1)^inv` (this branch); (2) `ℤ[i]`:
  the CP phase `C₄`/`90°` IS main's QR splitting (`d=5≡1 mod4 ⇒ (−1/5)=+1 ⇒ 5=(2+i)(2−i)`);
  (3) `ℚ(ζ₅)` Gauss periods (CP golden modulus + `C₄`) ↔ main's Teichmüller/`gauss_qr`;
  (4) Hodge-Riemann positivity `h=Q·J=I` ↔ main's `det_mul` (`det=1`). Richest:
  the permutation sign + Hodge-⋆ orientation + Legendre symbol + CP phase are one
  inversion/Gaussian object; the **Zolotarev** edge — now CLOSED
  (`ModArith/ZolotarevMuBridge.zolotarev_mu`, all odd primes) — closes the square.

- `gram_d2_prefactor` — **the α_em Gram self-energy `/d²` prefactor**.
  *Closed this session*: the cubic `25y³+1=25Xy²` is the correction ansatz
  `α²/d²` re-expressed (not a free form); the prefactor *value* is
  over-determined (three readings coincide at `d²`); the *mechanism* is
  identified — a degree-2 (2-point) object on the d=5 state space normalizes
  by `d²`, grounded in two convergent math structures (2-point operator-space
  dim `tensorDim d d` + 2-fold cup-graduation `cup_graduation_denom 1`).
  *Open*: (a) the remaining premise — a forcing theorem identifying the Gram
  self-energy *as* the `k=1` self-pairing cup term (promote
  `CupRingTrace`/`SelfPairingTrace` test → derivation); (b) derive the
  cup-graduation rule "each cup factor carries 1/d" from cup-ring axioms
  (currently a structural assertion). Anchors:
  `Lib/Physics/AlphaEM/{GramCubicReduction,GramD2Readings,GramD2Mechanism}`.

- `headline_precision_scope` — **what the Lean proves vs the README precision
  column**, headline by headline (extends the α_em DoF ledger). First finding:
  `m_μ/m_e` README "0.49 ppb" is PURE-proven only to the *leading integer
  bracket* (205); the ppb match is docstring numerics (leading α_em ppm bracket
  × Dyson tail `P` × δ's), inheriting α_em's DoF. Fair, not deception (atomic
  building blocks + recurrence argument real; gap = headline overstatement).
  Next: m_p (1.56 ppm), R_∞ (4.3 ppb), Koide.

- `ckm_rho_eta_apex` — **the CKM Wolfenstein apex `(ρ,η)` / Jarlskog
  magnitude**. Found auditing whether θ_QCD's `J` is derivable: J's
  *structure* is atomic (λ=5/22, A=φ/c, δ=π/φ²) but its *magnitude* is
  over-predicted ×2.66 (`J_DRLT=8.18×10⁻⁵` vs observed `3.08×10⁻⁵`) — the
  missing piece is the un-derived apex `(ρ,η)` (`s₁₃=Aλ³` omits
  `√(ρ²+η²)≈0.39`). A `CPViolation.lean` comment had masked this with an
  arithmetic error ("within 10%"); corrected.  **Multi-agent deep-dive (2026-06-08)**:
  the apex modulus `R_u=(NS−√d)/2=1/φ²` is the self-reference matrix's contracting
  eigenvalue; findings #2 (`disc=d` is *selection*, `FibonacciAtomicLock.
  disc_eq_atomic_sum_selects_shape`) and #4 (modulus = *de-signed square*,
  `apex_modulus_is_designed_square`) now ∅-axiom; item (a) (exact `ℤ[i]` CKM unitarity)
  closed (`Mixing/CKMExactUnitarity`).  **Open**: the `det=1`↔base-normalization arrow
  (apex modulus = `λ₋` of the CKM-from-`M` map); golden in the *radius* not the angle.
  Consumer: θ_QCD (`PRE_REGISTRATION.md` P2).
  **Update (2026-06-08)**: apex modulus `1/φ²` grounded as the self-reference
  Möbius contracting eigenvalue, and `1/φ²`-over-`φ²` now *forced* by `R_u<1`
  (`JarlskogApex.apex_modulus_subunit_forced`). **A₅ bridge marathon**
  (`lean/E213/Lib/Math/Algebra/Icosahedral/`, 14 PURE): the self-reference map
  `M` mod `d=5` is an order-5 element of `PSL(2,𝔽₅)≅A₅` (icosahedral) carrying
  character `φ` = the eigenvalue `φ²` via `φ²=φ+1` — grounds the open premise in
  established A₅ golden flavour symmetry. Still open: derive the apex *value*
  from an explicit A₅ generation assignment.

- **COUNT extremal combinatorics** — CLOSED ∅-axiom (LYM, Bollobás `bollobas_uniform`,
  Sperner ×3, Mirsky `mirsky_boolean`, Dilworth `dilworth_boolean`/`scd_card`, and the
  Leibniz determinant seed).  Promoted → `theory/essays/proof_isa/{chain_antichain_duality,
  counting_as_cardinality,sperner_double_counting,probabilistic_method}.md`.  No open seed.

- **determinant / permutation-sign** — CLOSED ∅-axiom (`PermSign.psign_mul`,
  `DetTranspose.det_transpose`, `DetMul.det_matMul`, `PermMatrixDet.det_permMatrix`); narrative in
  `theory/essays/algebra/{permutation_sign_as_homomorphism,determinant_as_quotient_characteristic,
  cayley_hamilton_self_characteristic}.md`.  ✓ *Done:* `det(permMatrix σ) = psign σ`
  (`PermMatrixDet.lean`, 11 PURE — the Leibniz sum collapses to the surviving `τ=σ` term via the
  nodup selector `sumZ_select`); the two readings of a permutation agree.  General **column
  Laplace** is also closed (`ColumnLaplace.cofactor_col_k`, 2 PURE — the `det_transpose`
  corollary: `minorAt k j Mᵀ` is defeq `transpose (minorAt j k M)` since row-skip = col-skip =
  `colShift`).  The `det_permMatrix` closure unlocks the **Zolotarev** bridge: `psign` of the
  multiplication-by-`a` value-list = the Legendre symbol (closed two ways — μ-block-decomposition
  `ZolotarevMuBridge` and primitive-root conjugation `ZolotarevCycle.zolotarev_full`).  *Open
  seed:* relocate the constructive pigeonhole (`firstDup`/`mem_of_card_le`/`cnt_filter_le`) to
  `Meta` (a cleanup, not a closure).

- `the_reframing_conquest` — **the standing target**: every agent (and most humans) re-imports a
  residue dichotomy, is corrected, repeats.  *Closed*: the root cause = the Lawvere–Cantor diagonal at
  the description scale (`why_the_reframing_recurs.md` essay + CLAUDE.md Residue-lint).  *Open*: the
  agent-fix, gated on an A/B question about the originator's cognition (different default percept →
  architectural reverse-polarity fix, vs. fast self-lint → meta-monitor + prior fix) — decidable only
  by a fresh instrumented introspective/RT probe, not from text.

- `residue_expression_atlas` — **the residue is expressed multi-directionally**, not by one
  mechanism (Cantor diagonal).  Cross-repo survey of the expression modes (non-surjection /
  fixed-point / forcing / graded cohomology) + the Minkowski-`?`-as-modular-cocycle arc.  Open
  side: the `c`-axis / face-axis unit wires; the finite(`d=5`)↔infinite(νF) regime synthesis; and
  (period sub-thread) the single irreducible **analytic atom** — the period value of a modular form
  over one unimodular symbol (integration, the period-relation generators, the slash action /
  weight-4 period polynomial `1−X²`, and the Manin contour decomposition all now ∅-axiom).  Closure
  records: `theory/essays/analysis/minkowski_as_modular_cocycle.md`,
  `theory/essays/foundations/reached_by_none.md`, and `Real213/{MinkowskiCocycle,MinkowskiGoldenExtremal,
  MinkowskiPeriodIntegral,MinkowskiHigherWeightPeriod,MinkowskiPeriodRelations,MinkowskiPeriodPolynomial,
  MinkowskiModularSymbol}` + `CupLadderResidueUnit`.
- **residue-unit `+1` dynamics** — CLOSED ∅-axiom (binary odometer + profinite `ℤ`-action +
  golden/Zeckendorf carry); narrative `theory/essays/foundations/{the_residue_unit_odometer,the_unit}.md`
  + `theory/math/algebra/phi_self_similarity.md` §3.7.  *Open seed:* a decidable carry-depth
  sub-classification (the eventually-periodic / finite-state end).
- **concept-pass open seeds** — the systematic "what does *naming an abstract
  concept* become under the 213 axiom?" pass (originator: Mingu Jeong).  Closed
  instances are permanent: König νF bridge (`KonigConditional`) + 2-adic/general-`p`
  νF escape (`Padic/NuEscape`) in Lean; the re-dressing / function-space readings in
  `theory/essays/foundations/{the_one_diagonal,the_reference_claim}.md`.  *Still open:*
  general-`p` one-carrier νF spine, ℝ one-carrier with König, and the next deep-dives
  (limit/completion, quotient/equivalence-class, actual-vs-potential infinity).

- `pure_lean_calibration_synthesis` — **infra frontier** (cross-campaign: determinant/sign +
  Reverse Math 213): the recurring core-`Decidable`/core-lemma **propext leak + hand-rolled-pure
  workaround** is now consolidated enough that a **`Meta/` propext-trap catalog** (which core
  constructs leak, which `*_pure`/`*213` replacement to use) is earned but **unbuilt — the open
  task**.  Plus the essay-trigger observation "classical hand-wave → explicit 213 object".

- `research_grade_closure_gate` — **meta-frontier**: `∅`-axiom is a
  necessary integrity check, not a sufficient *seriousness* check.
  Candidate "research-grade" closure gates (non-triviality/depth,
  iff-completeness, honest-status, reproduction-or-novelty, axiom-cost
  ledger, canonicality) curated for a later decision on whether to extend
  `theory/PROMOTION_CRITERIA.md`.  Candidates only — nothing adopted yet.

- `G167_crossdet_number_field_eisenstein_conjecture` — the cross-determinant
  classification's number-field reading; the Eisenstein/elliptic conjecture
  (originator: Mingu Jeong).  The proven core is closed in `lean/E213/`.
- `G121_dim4_self_pointing_axis` — the `d_M = d_213 − 1` geometrization ansatz;
  four open knots (M1)-(M4).  Side-observations feed
  `theory/math/geometry/geometrization_conjecture.md` (R1 closed; R1+ open).
- `betti_alpha_one_raw_lens` — synthesis: the "− 1" of `b₁ = NS² − 1 = 1/α₃`
  read as one Raw self-pointing under three Lenses (kernel constant /
  `SU(NS)` adjoint trace / self-pointing axis); seeds for the other forced
  constants and a `c`-dependent higher-`b_k`.
- `G123_padic_next_directions` — post-closure direction memo for the p-adic
  library (`theory/math/numbersystems/padic_real213.md`).  Directions A
  (explicit Teichmüller ω), B (μ_{p−1} root-of-unity + unit decomposition),
  G (general division) now **closed** in `lean`.  The remaining direction H
  (DRLT 5-adic content) is **CLOSED** — chapter
  `theory/math/numbertheory/fibonacci_5adic_valuation.md`
  (`archive/fibonacci_5adic/`).
- **p-adic closure harvest** — Teichmüller `ω(x)` + uniqueness + `μ_{p−1}×(1+pℤ_p)` decomposition
  + general division CLOSED ∅-axiom; chapter `theory/math/numbersystems/padic_real213.md` + essay
  `theory/essays/algebra/teichmuller_as_forced_fixed_point.md`.  *Open seed:* generalise the
  lift+fixed-point uniqueness engine to `sqrt` (`unique_of_lift_fixed`).  ✓ *Done:* the
  sequence-level **additive abelian group** (`SetoidAssoc.zp_add_setoid_group_capstone`); the
  **multiplicative** `ZpSeqEquiv` identities (`SetoidMul` — mul comm/assoc/one/distrib +
  `zp_setoid_commRing_capstone`); the shared **`Zp.diagLimit`** abstraction
  (`Foundation.diagLimit` + `diagLimit_trunc_succ` — the single diagonal-limit proof now
  factored out of `invFull`/`sqrtFull`/`teichmuller`, all three rewired to it).  ✓ **`i₅ =
  teichmuller(2-lift)` CLOSED** (`TeichmullerI5.i5_eq_teichmuller`, 5 PURE): `i₅⁴ ≡ 1` ⟹
  Frobenius-fixed `i₅⁵ ≡ i₅` ⟹ `teichmuller_eq_of_fixed` — the 5-adic imaginary unit IS the
  canonical `μ₄` Teichmüller representative of its residue, not an adjoined structure.
- `fibonacci_5adic_valuation` (**CLOSED** → chapter
  `theory/math/numbertheory/fibonacci_5adic_valuation.md`,
  `archive/fibonacci_5adic/`) — H: DRLT-specific 5-adic content.  H1 (5²⁵
  obstruction) settled-as-removed; H2/H3 (physics meaning / L-values) have
  no internal handle (recorded plainly per §5.4).  The admissible
  arithmetic-first move opened a full math arc at the ramified golden prime
  `5`: rank of apparition `α(5)=5` + Lucas-never-zero, the `ν₅≥1,2` FSM
  rungs, the quintupling identity `F_{5m}=F_m(25F_m⁴+25(−1)ᵐF_m²+5)`, and
  the all-orders law `ν₅(F_n)=ν₅(n)` (`fibN_val_law`).  Pure-math spinoff
  `i₅ ∈ μ₄` folded into the Teichmüller chapter + essay.
- `sums_of_squares_engines` — synthesis seed after four-square closure: the
  two representation engines (multiplicative root-bound vs. additive
  pigeonhole), and the next number-theory seeds (disc-`−8` congruence iff via
  the quadratic character of `2`; the three-square theorem as a hard
  out-of-both-engines frontier).
- **reciprocity as count-Lens** — QR + second supplement CLOSED ∅-axiom; narrative
  `theory/math/numbertheory/quadratic_reciprocity.md` + `theory/essays/proof_isa/counting_as_cardinality.md`.
  *Open seeds:* cubic/biquadratic reciprocity over `ℤ[ω]/ℤ[i]` (reuse `floor_sum_rectangle`'s
  lattice-count shape); fold `sumZ_swap` (Int) + the COUNT Nat double-sum into one `Meta`
  finite-Fubini.  ✓ *Done:* Zolotarev unification (`psign` sign side ↔ `gauss_qr` count side,
  one permutation two readouts) — `ModArith/ZolotarevMuBridge.zolotarev_mu`;
  `int_even_or_odd` deduplicated into `CenteredDivision`
  (FourSquare / QuadraticReciprocity now thin re-exports); the `two_mul_ne_one` clones remain.
- **Legendre-symbol package** — CLOSED ∅-axiom (54 PURE): Euler's criterion (`qr_iff_pow_one`,
  full iff `euler_criterion`), multiplicativity (`legendre_mul`), both supplements
  (`neg_one_qr_iff`, `second_supplement`), Gauss's lemma (`gauss_qr`/`gauss_mu`).  **Promoted** →
  `theory/math/numbertheory/legendre_symbol.md` (the QR chapter's base package).  ✓ *Done:*
  Zolotarev (`psign σ_a = (a/p)`, all odd primes) — `ModArith/ZolotarevMuBridge.zolotarev_mu`.

- **permutation's three readouts** (`permutation_three_readouts.md`) — cross-domain synthesis
  after merging the Legendre/QR package (main) into the determinant + p-adic branch.  Edge (1)
  ★ **CLOSED**; (2)–(4) open.  (1) ★ **Zolotarev** — the missing edge of "one
  permutation, three readouts" — `psign` (inversions) ≡ `det(permMatrix)`
  [`PermMatrixDet.det_permMatrix`] ≡ `(a/p)` [main, `gauss_qr`/`euler_criterion`]: **now a
  theorem for every odd prime** (`ModArith/ZolotarevMuBridge.zolotarev_mu` +
  `det_permMatrix_mulPermMod`); (2) the Legendre symbol as the 2-torsion projection of the
  Teichmüller `ω ∈ μ_{p−1}` (Euler's criterion = mod-`p` shadow of a `μ_{p−1}` identity); (3) the
  truncation tower `ZpSeq ↠ ℤ/pⁿ ↠ ℤ/p` reads the same ring-quotient (`SetoidMul` commRing) at the
  level where QR lives; (4) `(a/p)=1 ⟺ a has a `diagLimit` √ in ℤ_p` (Hensel face of the Legendre
  predicate).  Proven cores closed both sides; the edges are the work.

Closure records (promoted off this board):
- Lagrange's four-square theorem — **closed & promoted**:
  `∀ n, isSum4 ↑n` (`lean/E213/Lib/Math/NumberTheory/FourSquare.nat_isSum4`) +
  the additive-pigeonhole seed (`FourSquareSeed.four_square_seed`) → canonical
  `theory/essays/synthesis/four_square_additive_pigeonhole.md`.
- `G178_next_proofline_conjectures` (νF population + C-phys bridges + odometer cross-arc) —
  **closed** → canonical
  `theory/essays/foundations/{the_residue_as_primitive,the_frontier_has_a_form,the_residue_unit_odometer}.md`.
- `G182_completed_system_synthesis` ("the frontier (νF) has a form") →
  `theory/essays/foundations/the_frontier_has_a_form.md`.

## proof-ISA compilation series  — ★ CLOSED

The experiment (reproduce *solved* hard techniques by compiling them down the
proof-ISA, `seed/PROOF_ISA.md`) is **complete**.  Both named COUNT bounds are
proven ∅-axiom — `R(k,k) > N` (`Lib/Math/Combinatorics/RamseyNamedBound.ramsey_lower`)
and Sperner (`SpernerChains.sperner_theorem`) — with no new instruction forced
(COUNT's union-bound face and its double-counting dual).  König alone stalls, at
the non-constructive `DECIDE`.  The "why" archive is promoted to
`theory/essays/proof_isa/` (probabilistic, linear-algebra, parity, sperner,
könig, + the `what_is_a_proof` synthesis).

The catalog has since grown to **seven** lift archetypes (`ProofISALifts.lean`):
A6 FLOW + A7 POSITIVITY added (the cross-domain-conquest marathon), each driving
real ∅-axiom conquests.

- `G205_cross_domain_conquests_compilation` — the marathon's source note: the
  standing compilation table (history's cross-domain conquests lowered onto the
  proof-ISA; headline: cross-domain *is* REFRAME).  A6 FLOW + A7 POSITIVITY both
  ✅ closed from its candidate list.  **Residual open**: is POSITIVITY a GAP
  sub-mode or its own primitive; the per-conquest rows still pending ∅-axiom
  witnesses (S2 Weil weights, A6 index, …).

## A6 FLOW core / Ricci flow  (`ricci_flow_smooth_core.md`)

- `ricci_flow_smooth_core` — the smooth-metric general Ricci-flow core
  (Perelman `𝓕/𝓦`-monotonicity, surgery): the wall (Riemannian geometry + PDE,
  Mathlib-forbidden).  *Closed sub-steps*: round-sphere finite extinction,
  Einstein trichotomy, gradient-flow descent identity + completeness-LOOP.
  The **discrete** core is fully closed and promoted — rungs 1–12 incl. the
  four Perelman wall items, no-local-collapsing, χ²-entropy descent:
  `theory/math/geometry/discrete_perelman_core.md` +
  `theory/math/geometry/discrete_curvature.md` (ladder note archived to
  `archive/a6_ricci_core/`).  Only the smooth side stays open here.

## Transcendental functions  (`transcendentals/`)

- **Closure record** — the Lambert weld (`coth(1/q)` series ≡ CF, every probe,
  total modulus `k+2`; `exp(2/q)` unconditional) is closed ∅-axiom and promoted:
  `theory/math/analysis/lambert_weld.md` (`LambertBridge.lowerBase`,
  `weld_closed`; blueprint archived to `archive/transcendentals/`).
- `weld_crossdomain` — four bridges from the 2026-06-11 merge: CF
  partial-quotient growth as the ladder-rung invariant; inverse-avoidance
  by state-threading (the constructive response to the slot wall); the
  exclusion-depth ≟ separation-schedule unification brick; the pair-layer
  cross expression's three regimes (`=0` class / `=1` certificate / `≥1`
  separation).
- `transcendentals/weld_casoratian_development` — the proven `i`-invariant
  unimodular identity (`weld_casoratian`): flip criterion + ratio descent as
  theorems; a possible second, bridge-free certificate of `LowerBase`.
- `transcendentals/transcendental_functions_ladder` — convergent `exp/sin/cos/sqrt`
  as `Real213` functions with derivative rules (current: `exp` partial sum +
  stubs).  Rungs T1 exp-modulus → T2 sin/cos series → T3 derivative rules →
  T4 smooth sqrt → T5 identities.  One of the two hard blocks split off A6's
  smooth core; ordinary constructive analysis, in-reach ∅-axiom.

## PDE a-priori estimates  (`pde_estimates/`)

- `pde_estimates/discrete_pde_estimates_ladder` — the analytic engine behind
  Perelman monotonicity.  Goal = the **continuous** estimate, built 213-native as
  "discrete-uniform-in-mesh + modulus → `Real213` limit" (the conquest needs
  continuous, not discrete-graph).  Rungs P1 maximum principle → P2 oscillation
  decay → P3 energy/Dirichlet → P4 Li–Yau → P5 Shi.  P1–P3 reachable; P4–P5 the
  real depth.  Remaining wall = the smooth-manifold (chart/tensor) layer.
