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

## proof-ISA compilation series  (`G200_*`)

**The experiment:** reproduce *solved* hard techniques by compiling them down the
proof-ISA (`seed/PROOF_ISA.md`), to map the instruction set's interior and edge.
Mostly **closed** — the "why" archive is promoted to
`theory/essays/proof_isa/` (5 files: INDEX + probabilistic, linear-algebra,
parity, könig).  Cumulative finding: three surface-diverse methods collapse onto
the named eight (probabilistic + linear-algebra → COUNT; parity → READ ∘
SEPARATE), no new instruction forced; König **stalls** exactly at the
non-constructive `DECIDE` (the exterior).  COUNT registered as the quantitative
`GAP` sub-mode (`seed/PROOF_ISA.md`) + lift Archetype 4 (`ProofISALifts.lean`).

- `G200_probabilistic_method_count_compilation` — the COUNT discovery + the
  compilation verdict + the concrete lift status.

**Open rung (only):** the *named* `R(k,k) > 2^{k/2}` closure — pure `K_N`
bookkeeping (edge↔position indexing + `k`-subset enumeration giving `t=C(N,k)`,
then `erdos_schema`), **no new "why"**.  All engine pieces built ∅-axiom
(`CountExistence`, `RamseyLowerBound.{count_factor,mono_event_count,matchesC_count}`).

## the slash-reading atlas  (`G205_*`)

**The experiment:** render Mingu Jeong's "object IS the relation of two
distinct objects" (the slash) geometrically, varying the *reading* (directedness,
quotient amount, combining map, growth rule, readout) — the geometric face of
`06_lens_readings.md` §6.  Each setting gives a different shape and surfaces
different invariants.  Worked atlas + scripts: `research-notes/geometric/`
(`INDEX.md` is the live board).

- `G205_slash_reading_atlas` — core question: which readings are faithful to the
  Möbius form `P=[[2,1],[1,1]]` (surface `3,2,5,φ`) vs blind (symmetric averaging).
  Conjecture C1 (faithful ⟺ `det=1` glue preserved); nearest ∅-axiom target is
  `prim-distinct ⟺ linear independence` + the `arccos(−1/n)→90°` climb (K3).

## Kuratowski / planarity vs atomicity  (`kuratowski_atomicity.md`)

Does the 213 atomic signature sit on the 2-D planarity boundary by structure? `K_{m,n}` planar ⟺ `min≤2=N_T` (exact); `K_n` planar ⟺ `n≤4`, so `d=5` is the first non-planar (ceiling+1).  Both Kuratowski forbidden graphs (`K_5`, `K_{3,3}`) are 213 structures.  Speculative link to no-exterior (atomicity ⟺ non-flattenable).  Open: is there a derivation, or small-number coincidence with one exact hit?
