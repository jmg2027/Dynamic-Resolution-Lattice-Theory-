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

Closure record (the proven side of this arc):
`theory/math/analysis/{cf_holonomicity_hierarchy,phi_pi_poles}.md` +
`archive/analysis_depth/G183_holonomic_pointing_synthesis.md`.

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
**closed & archived** → `archive/spiral_axis/G181_atomic_spiral_adic.md`; built as
`Theory/Raw/{Odometer,OdometerValue}` + `Real213/ZeckendorfCarry`, narrated in
`theory/essays/foundations/the_residue_unit_odometer.md` + `theory/math/algebra/phi_self_similarity.md` §3.7.

## Real-completeness / intensional completability  (`completability/`)

**Core open problem:** completability as an intensional invariant — the
presentation/real split, and when a rate-free presentation (π) completes.

- `G169_intensional_completability_conjectures` — the presentation/real split
  + supporting ∅-axiom lemmas + the conjectures it opens.
- `G149_analysis_continuum_space_insights` — the analysis/continuum/space
  insight map feeding the completability and GRA programmes.

Closure record: `theory/math/{completeness_relocated,completeness_without_completeness}.md`
+ `theory/math/analysis/{holonomic_modulus,tower_native_completeness,refined_completability_engine}.md`.

## Sequence depth / multiplicative machinery  (`sequence_depth/`)

**Core open problem:** the multiplicative twin of the additive
finite-depth algebra (Hadamard product, Casoratian rank, holonomic `ℚ(n)`-orbit).

- `G188_depth_order_duality` — depth/order duality as the founding invert-twin
  at the sequence scale.
- `G188_multiplicative_conv_design` — `mconv` (multiplicative twin of `conv`):
  the power-sum/Newton route, with an honest ∅-axiom feasibility verdict.

Closure record: `theory/math/analysis/{divergence_depth_characterization,cfinite_orbit_dimension}.md`.

## Standalone frontiers (root of `frontiers/`)

- `count_substrate_synthesis` — the COUNT arc.  **CLOSED ∅-axiom**: LYM,
  Bollobás (`bollobas_uniform`), Sperner (×3), Mirsky (`mirsky_boolean`), Dilworth
  (`dilworth_boolean`/`scd_card` — the full SCD partition; narrative promoted to
  `theory/essays/proof_isa/chain_antichain_duality.md`).  Patterns: dual COUNT
  faces share one residue + the subset count `C(N,k)`; the
  `nodup`-`flatMap`-disjoint-fibre counting idiom; SCD partition without
  constructor injectivity; the propext/Classical tax on core arithmetic.  The
  Leibniz determinant seed (`det = Σ_{σ∈perms} sign(σ)·Π M i σ(i)`) is **CLOSED**
  through the full sign theory — see `determinant_closure_synthesis` below.

- `determinant_closure_synthesis` — post-closure harvest of the sign theory.
  **CLOSED ∅-axiom**: `PermSign.psign_mul` (the sign homomorphism, bubble-sort) and
  on it both `DetTranspose.det_transpose` (`det Mᵀ = det M`) and `DetMul.det_matMul`
  (`det(A·B) = det A·det B`, Cauchy–Binet + constructive `cnt`-pigeonhole); narrative
  in `theory/essays/algebra/permutation_sign_as_homomorphism.md`.  Patterns: the pure
  `cnt`-decision sidesteps the propext/Quot.sound `Decidable (a∈l)` instance;
  homomorphism-to-`{±1}` as a sorting invariant; one keystone → multiple capstones.
  **Open seeds**: `det(permMatrix σ) = psign σ` (the two readings of a permutation);
  general column Laplace expansion as a `det_transpose` corollary; relocate the
  constructive pigeonhole (`firstDup`/`mem_of_card_le`/`cnt_filter_le`) to `Meta`.

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
- `odometer_unit_synthesis` — post-closure synthesis of the residue-unit `+1`
  dynamics arc: patterns (single-primitive-as-full-dynamics; the ∅-purity
  pure-`Nat` trap catalog; carry-explicit over modular) + next seeds (promote
  `add_left_cancel_pure`/`lt_two_pow` to `Meta/Nat`; odometer `ℤ`-action ↔
  Markov/Stern-Brocot `SL(2,ℤ)`; a decidable carry-depth sub-class).
- `naming_abstract_concepts` — **deep-research candidate** (originator: Mingu
  Jeong): what does *attaching a term to an abstract concept* in standard math
  (ℕ, ℝ, ℚ_p, "limit", "completion", "uncountable", "set of all functions")
  become under the 213 axiom?  Working answer: naming = a residue-internal Lens
  event naming a **generation rule** (fold/coalgebra), never the completed
  totality; the abstract/infinite content is the νF escape; the classical
  "complete/decide" step is one single ∞-decision (capture), refused or carried
  as input.  *Closed instances:* König νF bridge (`KonigConditional`, 5 PURE) +
  2-adic νF escape (`Padic/NuEscape`, 4 PURE — ℤ₂ = König binary-tree branch, no
  finite Raw).  *Read-through:* ℝ/ℚ_p/König are one shape (dyadic / p-ary / general
  branching); ε-δ existential = first-nonzero-digit search = which-child-infinite =
  the same ∞-decision.  *Concept pass:* `concept_compactness.md` — compactness of
  dyadic `[0,1]` = König's binary lemma = the same `InfChildExists` import (theorem
  seed `FiniteSubcoverOracle ↔ InfChildExists`, now CLOSED as an ∅-axiom calibration —
  selection ⇒ compactness free, compactness ⇒ selection costs one LLPO step).  *Concept
  deep-dives:* `concept_compactness.md` (= the König wall), `concept_redressing_itself.md`
  (the re-dressing act = one more self-pointing; Lawvere/Yanofsky anchor; promoted to essay
  `the_one_diagonal.md`), `concept_function_space.md` (powerset = the self-cover's codomain,
  the CCC root of the diagonal).  *Next:* general-`p` νF escape, ℝ one-carrier, more
  concept deep-dives (limit/completion, quotient, actual-vs-potential infinity).

- `research_grade_closure_gate` — **meta-frontier**: `∅`-axiom is a
  necessary integrity check, not a sufficient *seriousness* check.
  Candidate "research-grade" closure gates (non-triviality/depth,
  iff-completeness, honest-status, reproduction-or-novelty, axiom-cost
  ledger, canonicality) curated for a later decision on whether to extend
  `theory/PROMOTION_CRITERIA.md`.  Candidates only — nothing adopted yet.

- `G167_crossdet_number_field_eisenstein_conjecture` — the cross-determinant
  classification's number-field reading; the Eisenstein/elliptic conjecture
  (originator: Mingu Jeong).  Closure record:
  `archive/completeness/G168_eisenstein_completion.md` (the proven core).
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
  is tracked in its own note `G124_padic_drlt_5adic`.
- `G125_padic_closure_synthesis` — post-closure harvest: the diagonal-limit
  constructor, `frobenius_lift` as a uniqueness engine, `ZpSeqEquiv` as the
  funext-free canonical equality (retiring direction C), and the reachable
  `i₅ = teichmuller(2-lift)`.
- `G124_padic_drlt_5adic` — H: DRLT-specific 5-adic content.  Terrain map
  (not a closure): H1 (5²⁵ obstruction) **settled-as-removed**
  (`RERESEARCH_n_u_removal.md`); H2 (i₅ physics meaning) / H3 (5-adic
  L-values) have **no internal handle** — recorded plainly per §5.4, no
  forcible map onto physics.  Pure-math spinoff `i₅ ∈ μ₄` (the 5-adic
  imaginary unit is a 4-th root of unity) CLOSED ∅-axiom and folded into the
  Teichmüller chapter + essay.
- `sums_of_squares_engines` — synthesis seed after four-square closure: the
  two representation engines (multiplicative root-bound vs. additive
  pigeonhole), and the next number-theory seeds (disc-`−8` congruence iff via
  the quadratic character of `2`; the three-square theorem as a hard
  out-of-both-engines frontier).
- `quadratic_reciprocity` — **CLOSED** strict ∅-axiom (`ModArith/QuadraticReciprocity.lean`,
  11 PURE).  `quadratic_reciprocity`: for distinct odd primes `p,q` (`m=(p−1)/2,n=(q−1)/2`),
  `(q QR mod p ↔ p QR mod q) ↔ (m·n) even`.  The complete Eisenstein route: `floor_qr` (Eisenstein's
  lemma `QR(a) ⟺ Σ⌊a·x/p⌋ even`, `p∤a`) ∘ `floor_sum_rectangle` (`Σ⌊qx/p⌋ + Σ⌊py/q⌋ = m·n`) ∘
  `parity_sum_iff`.  Promoted → `theory/math/numbertheory/quadratic_reciprocity.md`.
- `reciprocity_count_lens_synthesis` — cross-chapter synthesis after the QR closure: a classical
  sign is the parity bit of a named count; finite Fubini (`sumZ_swap`) appears twice unrecognised
  as one; "no point on the boundary" = `object1_not_surjective`.  Seeds: cubic/biquadratic
  reciprocity over `ℤ[ω]/ℤ[i]`, Zolotarev unification, a shared Int-parity home.
- `second_supplement` — **CLOSED** (`2` QR ⟺ `p ≡ ±1 mod 8`, `SecondSupplement.lean`, 8 PURE incl
  `gauss_mu`).
- `euler_criterion_converse` — Euler's criterion **CLOSED** strict ∅-axiom (full iff
  `aᵐ ≡ 1 ⟺ QR`, `ModArith/{EulerCriterion,EulerConverse}.lean`, 16 PURE; the converse =
  squares-list saturation of `RootBound.eval_zero`).  The note now tracks the **open
  downstream**: the quadratic character of `2` (second supplement), Gauss's lemma, and
  Zolotarev (`psign` sign side already PURE).  Promotion-eligible → `theory/math/numbertheory/`.

Closure records (promoted off this board):
- Lagrange's four-square theorem — **closed & promoted**:
  `∀ n, isSum4 ↑n` (`lean/E213/Lib/Math/NumberTheory/FourSquare.nat_isSum4`) +
  the additive-pigeonhole seed (`FourSquareSeed.four_square_seed`) → canonical
  `theory/essays/synthesis/four_square_additive_pigeonhole.md`; archived at
  `archive/four_square/four_square_marathon.md`.
- `G178_next_proofline_conjectures` (νF population + C-phys bridges + odometer cross-arc) —
  **closed & archived** → `archive/G178_next_proofline_conjectures.md`; canonical
  `theory/essays/foundations/{the_residue_as_primitive,the_frontier_has_a_form,the_residue_unit_odometer}.md`.
- `G182_completed_system_synthesis` ("the frontier (νF) has a form") →
  `theory/essays/foundations/the_frontier_has_a_form.md`; archived at
  `archive/G182_completed_system_synthesis.md`.

## proof-ISA compilation series  (`G200_*`)  — ★ CLOSED & archived

The experiment (reproduce *solved* hard techniques by compiling them down the
proof-ISA, `seed/PROOF_ISA.md`) is **complete**.  Both named COUNT bounds are
proven ∅-axiom — `R(k,k) > N` (`Lib/Math/Combinatorics/RamseyNamedBound.ramsey_lower`)
and Sperner (`SpernerChains.sperner_theorem`) — with no new instruction forced
(COUNT's union-bound face and its double-counting dual).  König alone stalls, at
the non-constructive `DECIDE`.  The "why" archive is promoted to
`theory/essays/proof_isa/` (probabilistic, linear-algebra, parity, sperner,
könig, + the `what_is_a_proof` synthesis).  Source notes archived to
`research-notes/archive/proof_isa/` (`G200`, `G205`).

The catalog has since grown to **seven** lift archetypes (`ProofISALifts.lean`):
A6 FLOW + A7 POSITIVITY added (the cross-domain-conquest marathon), each driving
real ∅-axiom conquests.

## A6 FLOW core / Ricci flow  (`a6_ricci_core/`, `ricci_flow_smooth_core.md`)

- `ricci_flow_smooth_core` — the smooth-metric general Ricci-flow core
  (Perelman `𝓕/𝓦`-monotonicity, surgery): the wall (Riemannian geometry + PDE,
  Mathlib-forbidden).  *Closed sub-steps*: round-sphere finite extinction,
  Einstein trichotomy, gradient-flow descent identity + completeness-LOOP.
- `a6_ricci_core/discrete_ricci_flow_ladder` — the 213-native route to actually
  closing A6's conquest: **discrete (Forman/Ollivier) Ricci flow** (combinatorial
  curvature, no smooth manifold).  Rung 1 done (`DiscreteRicci.formanEdge`,
  curvature↔topology); next: weighted Forman + flow step + convergence via
  `flow_reaches`.

## Transcendental functions  (`transcendentals/`)

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
