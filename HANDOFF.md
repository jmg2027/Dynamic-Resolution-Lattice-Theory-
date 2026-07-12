# Session Handoff — 2026-07-12

## Branch
`claude/fable5-research-topics-31wtzt` — a single-purpose divergence session: compile
~one year of research topics for successor sessions before a model transition.
No Lean changes this session; the deliverable is a research-program document.

## Headline — the year-horizon research program

**`research-notes/frontiers/research_program_year_horizon.md`** — the compiled program:

- **§0 Triage doctrine**: classify every target's kernel before attacking —
  W1 unsigned monotone count (bracketable, attack) / W2 signed cancellation
  (no count-Lens witness, map from below only) / W3 uniform-residue pointing
  (terminal, certify and stop) / W4 interface defect (re-specify and it falls).
  Extracted from the corpus's own wall post-mortems (Chebyshev, RH/PNT,
  Markov `H`, Banach).
- **Track A** — foundations: FTA on the Ω-descent, prime words as `Raw`,
  `DStr` Route B, the signed escape-pole census, native νF, rival corners,
  the simplicial `(NS,NT,d)` bridge, the `+`/`×` contest settled, universe audit.
- **Track B** — number theory: quartic reciprocity + the generic `μ_k` engine,
  supplementary laws, **Gauss reduction of binary quadratic forms** (the
  class-number object, mapping the Markov W3 boundary from below), the
  Euclid-witness atlas for Dirichlet-from-below, Jacobi `r₄(n)=8σ(n)` via the
  CD quaternions, Bernoulli/von Staudt–Clausen, PNT bracket narrowing, Pell units.
- **Track C** — analysis: ζ(3) numerator kernel (attack the route or certify W3),
  π conditional `(C,s)` capstone, `μ(x)` limsup cut, bare-interface completeness,
  discrete PDE ladder, Brick 8 fold-back iff, three-distance theorem,
  **finite Fourier on ℤ/n (recommended first topic — maximal connectivity)**.
- **Track D** — algebra/cohomology: Sq²/Adem, Massey H¹-triples, ∀(k,l)
  cup-Leibniz, E_n operad GRA, sedenion zero-divisors as residue readout,
  **representation-theory seed (S₃ character table → `8 = 3²−1` typed)**,
  **Galois-theory seed (the corpus's small fields, finally the correspondence)**,
  braid normal forms (cash the colimit verdict).
- **Track E** — physics: **E0 urgent — the θ_QCD falsifier consumes the
  un-derived Jarlskog J and its honest central value leaves its own bracket;
  repair or demote first.**  Then the Gram `d²` forcing (needs the ℚ-cup),
  `Zeta2Cut`, octet-via-representations, the Yukawa `Y_d(i,j)` assembly (the
  CP phase's missing leg; golden phase proven dead), Yang–Mills area-law
  reformulation (embedding-free or W3), neutrino Δm² *ratio* (untouched
  falsifier candidate), honest-K maintenance, wiring the proven Kähler
  skeleton, Weinberg running as typed hypothesis, the Schwinger `α/2π`
  bracket (g−2 sector entirely absent today).
- **Track F** — new-discipline seeds against the 12 verified structural
  absences: probability brackets (de Moivre–Laplace via `central_binom`),
  dyadic Fubini, the Lens 2-category, elliptic-curve group law as polynomial
  identity (Hasse stated as the W2 boundary), theta count shadows,
  reverse-math atlas as exposure, Zermelo/Sprague-Grundy, finite information
  theory (Kraft, entropy subadditivity).
- **Small-brick queue** (12 S-size warm-ups + Bertrand as the recommended
  first marathon), four-quarter sequencing, and the standing
  **do-not-attack list** (RH, PNT constant 1, Markov `H`, the universal
  no-exterior `∀`, Schanuel ceilings, "Δ⁴=spacetime"/"gravity=defect").

`research-notes/frontiers/INDEX.md` registers the note (top of Standalone frontiers).

## Grounding audits performed this session (4 parallel scans)
1. **Closed-corpus map** — what is formalized per cluster + the 12 verified
   absences (Galois/field theory, representation theory, general measure,
   functional analysis, Fourier, homotopy, smooth geometry, category theory
   as a domain, modular forms/L-functions, commutative algebra, model theory,
   PDE/variational).
2. **Physics precision honest table** — PURE-ratio vs PURE-bracket vs
   docstring-numerics classes per observable; the broken-θ_QCD finding; the
   clean parameter-free core (Koide, `1/c`, coupling ratios, `1/φ²`, mass gap).
3. **Open-frontier digest** — per-file open/blocked/size across the whole board.
4. **Foundations digest** — the 5 deepest tensions (universal floor not a
   theorem; completion-engine verdict "1 layer"; the `+`/`×` contest;
   form-agreement vs identity; residue as property vs noun).

## E0 executed — θ_QCD falsifier repaired (typed J, PURE)

`Couplings/ThetaQCD.lean` extended (17 PURE / 0 DIRTY, `lake build` of the
module + closure clean): the J input is now typed —
`native_J_below_bound` (the nEDM bound comparison survives DRLT's own
J = 8.18×10⁻⁵ at factor 2–3), `window_fails_with_native_J` (the
[251,300]·10⁻¹³ window provably fails under native J — the honest
downgrade as a theorem), `detectable_next_gen_either_J` (J-robust: next-gen
nEDM decides regardless of which J is right), bundled in
`theta_QCD_J_typed_core`.  `catalogs/falsifiers.md` F4 rewritten to match.
Remaining open: the J magnitude itself (the apex projection,
`ckm_rho_eta_apex.md` — program Track E4).

## E10 executed — first g−2 contact (Schwinger moment, PURE)

`AlphaEM/SchwingerMoment.lean` (9 PURE / 0 DIRTY; `lake build` of the full
381-module AlphaEM aggregator clean): `a_e^Schwinger = α/2π =
1161409×10⁻⁹` as integer arithmetic on the typed inputs (`pi_e9`,
`invAlpha_e9` — the `PiFiveGap` convention); the agreement with observed
`a_e` bracketed at [0.1%, 0.2%] (`agreement_bracket`); the gap
`1757×10⁻⁹` identified in the docstring as the shadow of the known QED
`C₂ = −0.328…` term (matches to ~0.8%) — deriving `C₂ = 197/144 + π²/12
− (π²ln2)/2 + 3ζ(3)/4` internally is the named next rung (ζ(3) machinery
exists: `Real213/Zeta3Cut`).  Catalog-sync for `physics-constants.md`
queued (new sector entry).

## E9 executed — the Weinberg 35 ppm claim made arithmetic (PURE)

`YangMills/WeinbergAngle.lean` extended (15 PURE / 0 DIRTY, module +
closure lake-built): the Class-B running-gap closure, previously
docstring numerics, is now integer arithmetic on the typed `pi2_e10` —
`v2_value_e7` (corrected sin²θ_W = 0.2312179 exactly),
`v2_gap_ppm_bracket` (**the gap to observed is in [30, 35] ppm** — the
35 ppm claim as a theorem), `v2_within_observed_window` (0.07σ) vs
`bare_outside_observed_window` (bare excluded at >1σ), bundled in
`weinberg_running_gap_typed_core`.

## S5 interval upgrade — CLOSED

`NeutrinoMassFloor.lean` + 2 theorems (15 PURE / 0 DIRTY):
`survives_joint_one_sigma_box` (the reading survives the entire joint 1σ
error box, hardest corner) + `kill_fires_solar_two_sigma` (the kill fires
on the solar +2σ line even at atmospheric +2σ) — the verdict is pinned
between 1σ and 2σ of the solar splitting, exactly JUNO's regime.

## S6 executed — sedenion zero-divisor census core (PURE)

`Levels/SedenionZeroDivisorCensus.lean` (10 PURE / 0 DIRTY, ~29 s build,
registered in the CayleyDickson aggregator): the L4 associativity-loss
census is fully rigid — **42 left pairs** (`a ∈ 1..7` octonion imaginary,
`b ∈ 9..15`, `b ≠ a+8`) × **exactly 4 partners** = **168** ordered
solutions (interpreter-verified full sweep; `168 = |PSL(2,7)|` recorded
as a Lens tag).  Kernel-certified: basis weld to the existing witnesses,
`pairCount(e₁+e₁₀) = 4`, and the three exclusions (octonion half, `e₈`,
conjugate slot `e₉`).  Queued: the 15-row `aCount` kernel ledger
(measured ~2 min/row, PURE — kept out of the always-built tree) and the
PSL(2,7) orbit-transitivity identification.

## Small brick #5 executed — the character↔spectrum weld at p = d = 5

`Geometry/DiscreteCurvature/KpCharacterEigen.lean` (7 PURE / 0 DIRTY,
aggregator + 60-module DiscreteCurvature build clean): the quadratic
character of `ℤ/5` — certified by `Eq`-only decide (square half,
non-square half, complete multiplicativity) — is mean-zero and hence a
`λ = 5` eigenfunction of the `K₅` Laplacian
(`quadratic_character_is_K5_eigenfunction`).  Bridge 1 of
`curvature_spectrum_crossdomain.md` closed at the atomic dimension.
**Propext trap logged**: the `Iff`+`∃` certification form pulls
`propext`/`Quot.sound` under `decide`; `Eq`/`Ne` restatement is PURE —
add to the `pure_lean_calibration_synthesis.md` catalog when built.
Open remainder: general-`p` transport (generator-enumeration bijection).

## Open Problems (priority order)
1. **Q1 of the program** — C8 finite Fourier → B2 generic `μ_k` engine →
   B5 Euclid-witness atlas → A4 escape-pole census → E7 honest K.
2. **Residuals** — the 5.71 provenance; the J magnitude (E4); the `C₂`
   internal derivation (g−2 rung 2); the S5 Σm_ν √-bracket; the S6
   15-row ledger + PSL(2,7) identification; the general-`p`
   character↔spectrum transport.
3. Everything else: see the program document's tracks and sequencing.

## Unresolved from this session
None structural.  The program document is tier-1 volatile: topics taken up
should get their own frontier notes; verdicts (especially W2/W3 filings)
should flow back into the §0 triage table.

## Also produced this session

- **`research-notes/frontiers/divergence_conjecture_slate.md`** — eleven
  sharp falsifiable conjectures with kill-tests (S1 crystallographic
  reciprocity ceiling, S2 CLT = modulus-degree rung 2, S3 the ℚ-cup with
  F₂ 2-torsion, S4 octet double-count isomorphism, S5 neutrino zero-dial
  mass-floor falsifier, S6 sedenion census, S7 Frobenius-splitting schema,
  S8 W1-completeness ledger, S9 three-distance/noble locus, S10 Kraft =
  complete tree, S11 Ramanujan ladder).  Recommended first: S5 (one
  session, adds an independent falsifier either way).
- **Four Phase-H marathon blueprints** (`blueprints/math/INDEX.md` Phase H):
  `18_finite_fourier_213.md`, `19_representation_213.md`,
  `20_galois_213.md`, `21_probability_brackets_213.md` — ready for
  `marathon-start`.

## S5 executed — first conjecture of the slate already decided (SURVIVES)

`research-notes/frontiers/neutrino_mass_floor_falsifier.md` + **new Lean**
`Lib/Physics/Mixing/NeutrinoMassFloor.lean` (13 PURE / 0 DIRTY, zero
imports, `lake build` clean, registered in the `Mixing` aggregator):
the zero-dial over-determination test survives —
`(m₁/m₂)² ∈ [0.038, 0.039]`, predicting `Σm_ν ≈ 61 meV`, `m₁ ≈ 1.7 meV`;
the kill line (`Δm²₂₁ ≥ 7.71×10⁻⁵ eV²` falsifies) sits ~1.4σ from the
current best fit — JUNO decides.  Bonus audit finding: F3's old anchor
`NeutrinoRatioDerivation` never existed; `catalogs/falsifiers.md` F3
corrected and now cites the new capstone.  Still open: provenance of the
5.71 ratio itself (docstring-only), interval-hypothesis upgrade, Σ bracket.
Full-build status: **`lake build E213` (519 modules) run at session end —
clean**, with all six new/extended modules of this session included
(NeutrinoMassFloor, ThetaQCD extension, SchwingerMoment, WeinbergAngle
extension, SedenionZeroDivisorCensus, KpCharacterEigen).

## Three-tier state
- **New**: `research-notes/frontiers/research_program_year_horizon.md`,
  `research-notes/frontiers/divergence_conjecture_slate.md`,
  `research-notes/frontiers/neutrino_mass_floor_falsifier.md` (tier-1);
  `blueprints/math/{18,19,20,21}_*.md`;
  `lean/E213/Lib/Physics/Mixing/NeutrinoMassFloor.lean` (tier-2, PURE).
- **Modified**: `research-notes/frontiers/INDEX.md`,
  `blueprints/math/INDEX.md` (registrations), `catalogs/falsifiers.md`
  (F3 corrected), `lean/E213/Lib/Physics/Mixing.lean` (aggregator),
  `HANDOFF.md` (this file).
- **Promotions**: none yet (the S5 core is a fresh closure; promotion per
  `theory/PROMOTION_CRITERIA.md` once the open thirds land).

## Next
Start Q1 (the sequencing section), or cherry-pick from the small-brick queue.
The previous session's number-theory momentum (quartic reciprocity via the
generic `μ_k` engine, B1/B2) remains the natural Lean continuation.
