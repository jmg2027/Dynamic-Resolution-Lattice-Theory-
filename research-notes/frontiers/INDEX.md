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
each Markov number determines a unique triple.

- `G173_markov_uniqueness` — the ∅-axiom arithmetic spine (neighbor
  congruence, √(−1) encoding, Button prime-power closure) + the conjecture
  slate reducing composite uniqueness to one realisability hypothesis `H`.
- `G172_lagrange_threads` — three approximation-spectrum threads
  (Stern-Brocot, φ/π extremes, Hurwitz cosines).
- `G174_markov_newton_synthesis` — idea-level graft of Markov uniqueness onto
  the Newton / Casoratian / FSM frameworks (Myhill–Nerode reading of the crux).

Closure record: `theory/math/analysis/{markov_uniqueness,markov_spectrum}.md`.

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
- `G181_atomic_spiral_adic` — design: the atomic spiral as a variable-base adic
  (carry = the residue unit).

Closure record: `theory/math/analysis/spiral_coordinate_classification.md`.

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
  library (`theory/math/padic_real213.md`).
- `G178_next_proofline_conjectures` — cross-arc conjecture seed / ranked agenda
  for populating νF (post-FSM).
- `G182_completed_system_synthesis` — "the frontier (νF) has a form" — an
  essay-in-waiting (candidate promotion to `theory/essays/` once reconciled).
