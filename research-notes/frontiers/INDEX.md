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

Closure record: `theory/math/analysis/{divergence_depth_characterization,cfinite_orbit_dimension}.md`.

## Standalone frontiers (root of `frontiers/`)

- `casoratian_axis_cp_crossdomain` — **the Casoratian / spiral-axis branch ↔ main's CKM
  CP-phase arc**.  **Both links now closed (∅-axiom):** (1) the morphism `φ:ℤ[i]→ℤ[J]` —
  floor rotation IS the Hodge `⋆`, one `C₄=ℤ[i]^×` (`Cohomology/Hodge/GaussianHodgeBridge`);
  (2) the companion-determinant sign `altSign(k−1)` IS the `psign` of the shift cycle, a fourth
  "permutation under three readouts" instance (`Cauchy/CasoratianPermSign`, also `=det(permMatrix)`).
  Insights promoted to `theory/essays/synthesis/{the_i_point_of_the_spiral_axis,
  the_permutation_under_three_readouts}.md`.  Archive candidate.
- `cp_crossdomain_insights` — **CP-phase cohomology ↔ main's sign/QR/cyclotomic
  campaigns** (merge marathon). Four candidate bridges where the two branches
  share one object: (1) the inversion sign is one object — `det(permMatrix)=psign`
  (main) = the signed Hodge cup wedge sign `(−1)^inv` (this branch); (2) `ℤ[i]`:
  the CP phase `C₄`/`90°` IS main's QR splitting (`d=5≡1 mod4 ⇒ (−1/5)=+1 ⇒ 5=(2+i)(2−i)`);
  (3) `ℚ(ζ₅)` Gauss periods (CP golden modulus + `C₄`) ↔ main's Teichmüller/`gauss_qr`;
  (4) Hodge-Riemann positivity `h=Q·J=I` ↔ main's `det_mul` (`det=1`). Richest:
  the permutation sign + Hodge-⋆ orientation + Legendre symbol + CP phase are one
  inversion/Gaussian object; the open **Zolotarev** edge closes the square.

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
  nodup selector `sumZ_select`); the two readings of a permutation agree.  *Open seeds:* general
  column Laplace as a `det_transpose` corollary; relocate the constructive pigeonhole
  (`firstDup`/`mem_of_card_le`/`cnt_filter_le`) to `Meta`.

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
  is tracked in its own note `G124_padic_drlt_5adic`.
- **p-adic closure harvest** — Teichmüller `ω(x)` + uniqueness + `μ_{p−1}×(1+pℤ_p)` decomposition
  + general division CLOSED ∅-axiom; chapter `theory/math/numbersystems/padic_real213.md` + essay
  `theory/essays/algebra/teichmuller_as_forced_fixed_point.md`.  *Open seeds:* the concrete
  `i₅ = teichmuller(2-lift)` theorem (via `teichmuller_unique`); generalise the
  lift+fixed-point uniqueness engine to `sqrt` (`unique_of_lift_fixed`).  ✓ *Done:* the
  sequence-level **additive abelian group** (`SetoidAssoc.zp_add_setoid_group_capstone`); the
  **multiplicative** `ZpSeqEquiv` identities (`SetoidMul` — mul comm/assoc/one/distrib +
  `zp_setoid_commRing_capstone`); the shared **`Zp.diagLimit`** abstraction
  (`Foundation.diagLimit` + `diagLimit_trunc_succ` — the single diagonal-limit proof now
  factored out of `invFull`/`sqrtFull`/`teichmuller`, all three rewired to it).
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
- **reciprocity as count-Lens** — QR + second supplement CLOSED ∅-axiom; narrative
  `theory/math/numbertheory/quadratic_reciprocity.md` + `theory/essays/proof_isa/counting_as_cardinality.md`.
  *Open seeds:* cubic/biquadratic reciprocity over `ℤ[ω]/ℤ[i]` (reuse `floor_sum_rectangle`'s
  lattice-count shape); Zolotarev unification (`psign` sign side ↔ `gauss_qr` count side, one
  permutation two readouts); fold `sumZ_swap` (Int) + the COUNT Nat double-sum into one `Meta`
  finite-Fubini.  ✓ *Done:* `int_even_or_odd` deduplicated into `CenteredDivision`
  (FourSquare / QuadraticReciprocity now thin re-exports); the `two_mul_ne_one` clones remain.
- **Legendre-symbol package** — CLOSED ∅-axiom (54 PURE): Euler's criterion (`qr_iff_pow_one`,
  full iff `euler_criterion`), multiplicativity (`legendre_mul`), both supplements
  (`neg_one_qr_iff`, `second_supplement`), Gauss's lemma (`gauss_qr`/`gauss_mu`).  **Promoted** →
  `theory/math/numbertheory/legendre_symbol.md` (the QR chapter's base package).  *Open seed:*
  Zolotarev unification (`psign` sign side ↔ `gauss_qr` count side, one permutation two readouts).

- **permutation's three readouts** (`permutation_three_readouts.md`) — cross-domain synthesis
  after merging the Legendre/QR package (main) into the determinant + p-adic branch.  Four open
  bridging edges between the two campaigns: (1) ★ **Zolotarev** as the missing edge of "one
  permutation, three readouts" — `psign` (inversions) ≡ `det(permMatrix)` [now proven,
  `PermMatrixDet.det_permMatrix`] ≡ `(a/p)` [main, `gauss_qr`/`euler_criterion`], closed by
  `psign (×a mod p) = (a/p)`; (2) the Legendre symbol as the 2-torsion projection of the
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

## proof-ISA compilation series  (`G200_*`)  — ★ CLOSED

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
