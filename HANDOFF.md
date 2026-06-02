# Session handoff

Branch: `claude/depth-arc-completeness-iEMpZ` (merged with `main`; adds the
real-number depth-arc / holonomic-modulus thread on top of the Lens-rebuild main).

Durable closed work lives in `lean/E213/` (source of truth) and `theory/`
(narrative); `catalogs/`, `STRICT_ZERO_AXIOM.md`, and `research-notes/` carry
status + scratch.  This file keeps the current open targets, the closed index,
and hygiene notes.

## State

The **Lens tree is 0 real DIRTY** (sealed-by-design = the `Prop`-atom thesis
only: `propAsDistinguishing*` / `canonical*Map` / `BoolProp.universalMorphism_commute_*`,
where `propext` *is* the content).  213's equivalence is unified on
reading-equivalence: `ReadingEq.same` is the canonical sameness, Lean `=` its
realization at concrete codomains, pointwise `↔`/`sameLens` where `=` would
import `funext`/`propext`.  Full build (1533 modules) clean.

## OPEN — targets

### Validation core — the DRLT Standard (the real target)

`CLAUDE.md` "DRLT Validation Standard": from `(NS, NT, d) = (3, 2, 5)` atomicity,
0 free parameters, satisfy at least one strict ∅-axiom result —
  - **precision theorem** at ppb–ppm: `1/α_em`, `m_μ/m_e` (`NS·137/NT`, 0.48 ppb),
    `m_p` (`NS·Λ_QCD·P`), `R∞` (4.3 ppb), `Ω_Λ` (0.0008 %);
  - **falsifier** (measurable): `N_gen = C(NS,NT) = 3`, `θ_QCD ∈ [2.5,3.0]×10⁻¹¹`,
    neutrino normal ordering, Cabibbo `λ = 5/22`.

Catalogs: `catalogs/{physics-constants,falsifiers}.md`.  **Real target**: precision
theorem AND falsifier for the same observable.  Next concrete step: audit which
of these are *strict ∅-axiom* in Lean vs which are still Python/numerical or
carry gaps (e.g. `AlphaEM/GramStructuralCapstone` for `1/α_em`).  Foundational
hygiene must not displace this.

### CayleyDickson remaining (category D)

  - `Trig.conj_mul_anti` — needs `NonAssocStarRing213 Sedenion` (a Sedenion→
    `CDDouble Cayley` bridge replicating `CayleyAlgebra213`; the parametric CDDouble
    star instance needs `[StarRing213 α]` and Cayley is non-associative, so a
    manual route), then the structural proof (cf. `SedenionHeavy.conj_mul_anti`).
  - `SedenionHeavy.flexible` — the `CDDoubleFlexible` cross-pair open item
    (`cd_flexible` needs base alternativity, which Sedenion's Cayley base lacks).

### Depth-arc — real-number / completeness thread (this branch, current)

**Branch scope: real-number topics only.**  (Non-real tracks — the GRA/CD tower
duality and Cayley-Dickson algebra — belong on a separate branch; see link E.)

The depth arc (real = decision procedure, completeness relocated; 13 links) is
closed + promoted (`theory/math/completeness_without_completeness.md`).  Extensions
A–D + B are now **all closed ∅-axiom this arc**:

  - **A. `depth_floor_is_det_one`** — DONE this prior arc (`Cauchy/DepthFloorDetOne`,
    7/0): forward (`convergent_crossdet_floor_is_one`) + converse
    (`floor_one_is_P_invariant` = `pellNormStep`).  The floor IS the P-orbit
    invariant.  Hinge between analysis-ladder and atomic forcing.
  - **B. finite-depth recurrence formal** — DONE FULLY (general theorem + e + π) this
    arc.  **General theorem** (`Cauchy/DepthPRecursiveInstances`, 23/0):
    `newton_polyDepth` — *every* degree-`d` discrete polynomial `Σ_{i≤d} cᵢ·binom(·,i)`
    (Newton form, 213-native `binom`, Pascal) has `polyDepth d`; exact Newton-basis
    difference (`diff_newton` lowers degree by one, iterated `d`× via `liftK_congr` +
    `liftK_diff_comm`).  `binomCol_polyDepth` = single-column case.  **e closed**:
    `e_finite_depth_iff_P_recursive` = order-1 recurrence + `polyDepth 1` ratio.
    **π closed**: `DepthPiQuartic.piRatio_polyDepth` — the full degree-4 cross-det
    ratio `4(n+1)²(2n+1)(2n+3)` has `polyDepth 4` (4 differences → const `384`),
    confirming π depth 6 ∅-axiom.  The nonlinear-Nat expansion is discharged by the
    new reflection prover **`Meta/Nat/PolyNat`** (`poly_id`, 11/0): the ∅-axiom `ring`
    replacement — reify to a polynomial tree, normalise to Horner coeffs, equal lists
    ⟹ equal by `rfl`.  Reusable helpers live in their fundamental homes:
    `add_sub_add_of_le` in `Meta/Tactic/NatHelper`, `liftK_congr` in
    `Cauchy/DepthPRecursive` (pointwise-equality lift, no `funext`), `poly_id` in
    `Meta/Nat/PolyNat`; `binom_mono` stays with the Newton-basis machinery in
    `DepthPRecursiveInstances`.
  - **HolonomicReal type architecture** — AUTONOMOUS CASE DONE this arc
    (`Real213/HolonomicReal`, 8/0): `HolonomicReal` bundles a holonomic recurrence
    spec + the convergent `CauchyCutSeq` (modulus `seq.N` as a *constructed field*,
    not a hypothesis) + `ValidCut` of the limit; `HolonomicReal.cut_valid` is the
    unconditional API.  φ is a complete instance (`phiHolonomicReal`): order-2
    constant-coeff (det 1), modulus `N(m,k)=2k` (proven, `phiConvergentSeq`), cut =
    closed-form `phiCut`.
  - **e — TOTAL constructive modulus, complete `HolonomicReal`** this arc
    (`ExpLog/EulerModulus`, 11/0, deriving from `RateModulus` — no bespoke engine):
    `euler_total_modulus` / `euler_cut_const` — `eulerCut`
    is constant past `k+2` for every `(m,k)`, `k≥1`; `N(m,k)=k+2` explicit.  `eHolonomicReal`
    bundles it (modulus a constructed field, like φ).  Mechanism: margin invariant
    `e_i + 1/(i·i!) ≤ m/k`, forward step `i(i+2)≤(i+1)²` (0≤1, via `PolyNat`); the
    denominator gap `≥1/(k·(k+1)!)` beats the tail `<1/((k+1)·(k+1)!)`; the side is
    read off the decidable `eulerCut (k+1) m k`.  **Breaks the earlier "LEM wall"
    reading** (`G164` revised): the wall is for *rate-free* sequences; e's factorial
    rate escapes it — no irrationality measure needed.  `ExpLog/EulerCertifiedBracket`
    (3/0) is the elementary bracket-witness view of the same Cauchy property.
    `eHolonomicReal_cut_stable`: the holonomic cut is the stable convergent value
    (e analogue of `phiHolonomicReal_cut`).  FRONTIER criterion (`research-notes/G165`):
    a FREE total modulus `N≈k` exists iff `tail_i · k · d_i < 1` at `i≳k` (rate beats
    the denominator-gap quantum).  e meets it (factorial rate `1/(i·i!)` vs gap
    `1/(k·i!)`: ratio `k/i<1`); **π-via-Wallis does NOT** (tail `~1/n` vs fast
    `wallisDen` → needs π's irrationality measure `μ(π)≤7.1`, genuinely hard — a fast
    π series is the real route).
  - **General generator — DONE** this arc (`Real213/RateModulus`, 4 PURE):
    `rate_total_modulus` — *any* monotone convergent cut-sequence `a_i/d_i` with a
    non-increasing margin `e_i + 1/(i·d_i)` (the rate certificate `Htel`) has a total
    ∅-axiom modulus `N(m,k)=k+2`; the step is pure transitivity once `Htel` is
    isolated.  **Validated on e**: `euler_cut_const`/`euler_total_modulus` are direct instances of `rate_cut_const`, via
    `euler_{Htel,hmono,hmonoS}`).
  - **Depth-rank ⟶ rate-certificate bridge — DONE** this arc
    (`RateModulus.Htel_of_crossdet`): `Htel` has a closed form in the
    **cross-determinant** `W_i = a_{i+1}d_i − a_i d_{i+1}` — it holds iff
    `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}` (W small vs the denominator's discrete
    growth).  e instantiates it directly — e's cross-det IS `eulerDen` (`euler_cross_det`),
    so `euler_Htel` is now *derived from the cross-determinant*, not a bespoke estimate;
    the depth arc (W) and the modulus generator (Htel) are one mechanism.  Narrative:
    `theory/math/analysis/holonomic_modulus.md`.
  - **Tower-native completeness program — CLOSED + PROMOTED** this arc.  Completability
    = comparison of two growth-axes (cross-det `W` vs denominator `d`) inside the tower;
    narrative `theory/math/analysis/tower_native_completeness.md`, capstone
    `Real213/TowerNativeCompleteness.tower_native_completeness_program`.  Four new PURE
    modules:
      - **T1 boundary** (`Real213/CrossDetOvertake`, 11/0): `CrossDetSmall W d`
        (`i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`); below ⟹ free
        (`crossdet_small_total_modulus`, `N=k+2`; free bottom = constant `W=1`); above ⟹
        broken (`overtake_breaks`; witness `dexp_overtakes_denom`, `2^{2^i}` overtakes
        `2^i`).  `completability_boundary`.
      - **T2 Liouville** (`Real213/LiouvilleModulus`, 13/0): recurrence convergents
        (`g_k=c^{k·k!}`) have `W_k = liouDen_k = c^{k!}` (`liou_cross_det`, the e
        pattern); factorial denominator dominates ⟹ `CrossDetSmall` ⟹ free modulus
        (`liouville_total_modulus`).  `liouville_W_eq_denom_coordinate`: `W` and `d`
        share the factorial coordinate, `d` dominates — value-axis depth-∞ irrelevant.
      - **T3 closure** (`Cauchy/DepthClosure`, 16/0): `diff` linear (`diffN_add`) ⟹
        finite-difference-depth class closed under `+` (`finDiffDepth_add`), values under
        `×` (`value_mul_closed`, `c^{e1+e2}=c^{e1}·c^{e2}`); exponent axis lifts depth
        (`value_finRatio_of_finDiff`) and breaks at `2^{2^n}` (`exp_axis_breaks`).
      - **T4 generator** (`Cauchy/DepthCoordGenerator`, 10/0): `genExp d = binom·d`
        realizes diff-depth `d` (`genExp_realizes`), `genValue` lifts to ratio-depth `d`,
        `expTower` populates the `ω^r` heights — `tower_is_coordinate_system`.
      - **tie**: the tower has no top = the residue (`DepthCeilingResidue`).
    Follow-on results (agent-collaboration round): **W=d unification**
    (`Real213/CrossDetEqDenom`, 3/0): `crossdet_eq_denom_total_modulus` — one theorem
    behind e and Liouville (both reproven as one-liners). **Sharp growth-rate threshold**
    (`Real213/GeometricThreshold`, 6/0): **exact iff** `geom_boundary_iff` —
    `CrossDetSmall (r^·) (q^·) ↔ r < q` (for q≥2).  Free side all i≥1
    (`geom_crossdet_small`); broken side (`geom_crossdet_overtake_sharp`, every `q≤r`)
    at the single fixed witness `i=q`.  Corrects the naive `r≤q` — equal-rate `r=q`
    fails, the polynomial factor `i(i+1)` outliving the single denominator factor `q`.  **Depth-exactness** added
    (`DepthPRecursiveInstances.binomCol_depth_exact`, `DepthCoordGenerator.genExp_depth_exact`):
    the binomial column floors at *exactly* `d`, so T4's "surjective generator" is now a
    theorem, not a docstring claim.  W-relation rungs: `{W const (algebraic), W=d
    (e/Liouville)} ⊆ CrossDetSmall` (free), threshold `r<q` for geometric, overtake breaks.
    **W=const rung** (`Real213/CrossDetConstDenom`, 13/0): `crossdet_const_total_modulus`
    + φ as named instance (`phi_total_modulus_via_const`) — φ's even-Fibonacci convergents
    `fib(2i+2)/fib(2i+1)` have constant cross-det `1` (Cassini unit) and φ²-step denominator
    growth beating `i(i+1)` for all i≥1, so φ completes through the same bridge as e/Liouville.
    **W=d line = reciprocal-series reference family** (`Real213/ReciprocalSeries`, 12/0):
    `W=d` cross-divides to `a_{i+1}/d_{i+1} − a_i/d_i = 1/d_{i+1}`, so the rung is exactly
    `Σ 1/d_j`, a one-parameter family indexed by the ratio `g_i = d_{i+1}/d_i` (`den`/`num`
    from `g`, `recip_cross_det` = W=d by construction); `recip_total_modulus` — free iff
    `i+1 ≤ g_i`.  e = linear-ratio point `g_i=i+1` (`den_linear_is_factorial`: denominators
    = `j!`); Liouville = fast-ratio points.  Originator's reading: the diagonal `y=x` of the
    (W,d) plane is a growth-graded reference family of self-completing reals, each named by
    its ratio sequence.  Open: universal reciprocal-series chart (every real has such a
    representation — Engel/Sylvester).
    **Presentation-dependence** (`Real213/PresentationDependence`, 6/0):
    `crossDetSmall_is_presentation_dependent` — `rcut` is rescaling-invariant
    (`rcut_rescale`, the cut cancels a common factor `c`) while `CrossDetSmall` is not
    (cross-det scales `c²`, denom `c`); e's `×2` representation `2·eulerNum/2·eulerDen`
    is the *same real* yet fails `CrossDetSmall` at `i=1`.  The "deficiency of the
    presentation, not the real" thesis as a theorem.  Also `overtake_breaks_at`
    (`CrossDetOvertake`): the overtake break at any single witness index `i₀≥2`.
    **Completability is a lex `(height, rate)` grade** (`Real213/CompletabilityGrade`,
    3/0, reals-only refinement): not binary but ordinal `ω·height + rate`.
    `height_two_overtakes` — double-exp `q^{b^i}` over single-exp `q^i` breaks
    `CrossDetSmall` for *any* base (up one exponential height ⟹ broken regardless of
    rate); `height_one_under_height_two` — single-exp over double-exp always free (down a
    height ⟹ free); `geom_boundary_iff` — within a height, free ⟺ `r<q`.  `completability_grade`
    bundles the three: **height dominates rate.**  `height_is_omega_coordinate`: every exponential-tower step up (`expTower` level `r`) overtakes, so height is a genuine ω-indexed coordinate (not just {1,2}). First rung of the refined real engine: completability graded into a transfinite ordinal.
    **Intensional gauge axis** (`Real213/IntensionalCompletability`, 3/0): `crossdet_rescale_antitone` (CrossDetSmall (c²W)(c·d)→CrossDetSmall W d, c≥1 ⇒ gcd-reduced presentation canonical) + `modulus_rescale_invariant` (completion is gauge-invariant = the cut's truth) + `completability_is_intensional`. Refined engine = (ordinal height) × (rate) × (intensional gauge class); cut = gauge collapse, canonical grade read on the reduced representative.
    **Synthesis + ε₀ cap**: `Real213/RefinedCompletabilityEngine` (`refined_completability_engine`, 1/0) bundles both axes (ordinal height + ω-coord + test-antitone + truth-invariant) as one engine. `Real213/HeightTowerResidue` (2/0): `height_tower_no_top` (diag(expTower q) escapes every level) + `height_tower_residue` (the height ω-tower has no top; its diagonalization IS the pointing/Cantor residue, `ceiling_reference_leaves_residue`). Floor (bottom) ↔ residue (top) close into one self-cover loop — the refined real engine has no exterior.
  - **CF universality — the det-one floor is universal + universal completion** (`Real213/ContinuedFractionFloor`, 17/0 + `Real213/ContinuedFractionModulus`, 16/0): for ANY partial-quotient sequence `a`, the continued-fraction convergents `cfP/cfQ` (over Int) have cross-determinant `cf_det_sq`: W_n² = 1 — the universal Cassini engine `cf_det_step` (W_{n+1} = -W_n, the q=1 case via `cassini_one` over any CommRing213). So EVERY real, via its continued fraction, sits on the W=±1 det-one floor; `FibCassiniNat`(φ) is the all-1s instance. Rate engine: `cfQn`/`cfQn_pos`/`cfQn_fib` (denominators as Nat, positive, Fibonacci-growing q_{n+2}>=q_{n+1}+q_n => gaps 1/(q_n q_{n+1}) shrink), `cfQ_eq_cast`. Even two-step cross-det `cfDet2_even`: W'_{2n} = p_{2n+2}q_{2n} - p_{2n}q_{2n+2} = a_{2n+2} (the +1 even floor amplified to the quotient via the general `det2_ring`). **Universal completion CLOSED** (`ContinuedFractionModulus`): `cf_universal_total_modulus` — every real ≥ 1 carries a free total ∅-axiom modulus N(m,k)=k+2 through its CF even convergents. Pieces: `cfPn`/`cfP_eq_cast`/`cfPn_pos` (Nat numerators), `cfDet2_even_nat` (Nat descent by ofNat-inj), `cfQn_ge_self` (n≤q_n), `mono_of_step`/`ratio_trans_gen` (reusable single-step⟹across-layer monotonicity), `cf_h{d,pos,W,monoS,cs,mono}` (the CrossDetSmall bridge hyps; smallness reduces to i≤q_{2i+1}). This is `CrossDetConstDenom.phi_total_modulus_via_const` lifted off Fibonacci onto an arbitrary partial-quotient sequence — the algebraic-φ completion generalised to the whole real line. CF = the expansion engine at its terminus: distinction (floor) leaves a unit residue, that residue is the next operand (x|->1/(x-floor)), gapless because the unit W=±1 is indivisible + the denominator outgrows it.
    Outside the tower-native frame (not claimed): full num/den closure under `+`/`×` for
    arbitrary rate-carrying presentations; a generic ordinal-indexed `coord→cut`.  Next
    instance: a fast π representation meeting the rate criterion.
  - **Eisenstein/elliptic conjecture — discriminant-sign core LANDED** (`research-notes/G167`).
    The `(W,d)` classification's number-field reading: golden form `m²−mk−k²` (disc `+5`,
    indefinite, ∞ units → convergent *line*) vs Eisenstein norm `a²−ab+b²` (disc `−3`,
    definite, 6 units → *torus* = `j=0` elliptic-curve lattice).  New ∅-axiom modules:
      - **`Meta/Int213/PolyInt2`** (22/0): a **bivariate `Int` polynomial-identity
        reflection prover** (two Horner layers + `neg`; the `Int` analog of `PolyNat`,
        which is `Nat`-only/univariate).  The repo had **no** pure `Int` ring tactic
        (`quad_norm` = `simp`+`omega`-dirty); `poly_id2` closes bivariate `Int`
        identities by `rfl`.  Reusable repo-wide.
      - **`CayleyDickson/Integer/EisensteinSignature`** (13/0): `eisenstein_norm_posdef`
        (positive-definite, via `two_eisForm` by `poly_id2` + `sq_nonneg` by Int
        constructor-cases); `signature_dichotomy` (Eisenstein definite vs golden
        indefinite = curve vs line); `eisenstein_det_one_floor` (norm-1 floor is
        multiplicatively closed = the 6-unit group `= NS·NT`, the Eisenstein analog of
        φ's Cassini det-one floor — reuses `ZOmega.normSq_mul`, which is in fact PURE
        despite its stale `[propext]` docstring).
    Out of scope (the edifice 213 declines): elliptic curves / CM / modular forms /
    the `j`-map / modularity (the geodesic-folding picture stays conceptual in G167).
      - **Eisenstein cross-determinant over ℤ[ω] — BUILT** (`CayleyDickson/Integer/
        EisensteinCrossDet`, 14/0): `crossDet a d n = a_{n+1}d_n − a_n d_{n+1} ∈ ℤ[ω]`;
        `cassini_ring` (the ring identity, manual `calc` over the pure `Ring213`/
        `CommRing213` API — no normalizer exists); `crossDet_step` (Cassini engine
        `W_{n+1} = −q·W_n`); `crossDet_normSq_step` (`‖W_{n+1}‖² = ‖q‖²‖W_n‖²`);
        `crossDet_unit_floor` (q, W₀ units ⟹ ‖W_n‖²=1 ∀n — the det-one floor preserved);
        `crossDet_on_units` (each W_n is one of the **6 units**, via
        `normSq_one_in_units6`); `omegaFib_on_units` (concrete `s_{n+2}=s_{n+1}+ω·s_n`,
        `q=ω`).  The Eisenstein analog of φ's Fibonacci–Cassini `W=±1` (the 2 units of
        ℤ): over hexagonal ℤ[ω] the cross-det floor is the order-6 unit group.
  - **C. third-axis closure** — DONE this arc (`Cauchy/DepthOmegaTower`, 13/0):
    `coord_wf` — the depth-`r` tower coordinate (`r`-fold nested lex product
    `Coord r`) is well-founded for every `r`, an ordinal `< ω^r`; the whole `ω^ω`
    ladder, level by level (`coord_wf 2` recovers `DepthOrdinal`'s `ω²`).
    `coord_layer_dominates` — each exponential layer ×`ω` (one larger leading
    coeff outranks the entire lower tower).  Positive sequence companion to
    `dexp_not_const`: `dexp_exponent_floors` (the double exp's *exponent* floors
    under one ratio) + `expTower`/`expTower_succ` (value sits one `expSeq` above
    the shorter tower).
  - **D. Liouville's coordinate** — DONE this arc (`Cauchy/DepthLiouvilleCoord`,
    9/0): `liouville_exponent_coordinate` — `ratioLift fact n = (n+1)!/n! = n+1`
    (super-poly `k!` → linear in one ratio), `diff (ratioLift fact) = 1` (one diff
    floors it), `diff fact n = n·n!` (never floors on the diff axis alone).  So
    `c^{k!}`, with no finite `(h,d)`, has ratio-depth 1 / diff-depth 1 one
    recursion tier down — the concrete frontier toward `ε₀`.  PURE factorial
    (Lean-core `Nat.factorial` is Mathlib); division-cancel via `mul_div_self_pure`.
  - **E. tower duality (GRA↔CD)** — OUT OF SCOPE for this branch.  It is a bridge to
    the non-associative-algebra track (`CayleyDickson/`, `Meta/Algebra213/`), not a
    real-number topic, and is an unproven conjecture (`gra_book.md` 5.3.1).  The
    depth-floor `5 = NS+NT` vs CD-dimension `5` is a meaning-by-analogy that the
    framework refuses, not an earned correspondence.  Belongs on a separate CD/GRA
    branch (its open `CDDoubleFlexible` cross-pair attack was logged then descoped;
    see git history if that track resumes).


### Scoped doc follow-ups (judgment / generative)

Candidate merges (`theory/lens/{properties,cardinality,instances,axiom_lenses}` →
`properties_catalog`; `theory/physics/{atomic_base,atomic,capstones}`).  The
real-number chapters are well-classified as they stand: `completeness_without_completeness`
is one coherent 13-link arc, `holonomic_modulus` the constructed-modulus mechanism,
`real_without_completeness` the on-demand essay — no split improves them.

## Closed (durable homes — do not re-derive)

| Topic | Source of truth | Narrative |
|---|---|---|
| Equivalence unification — 213's sameness is reading-equivalence (`ReadingEq.same`); `HasDistinguishing` stated over `same`; composite instances thread `same` (`Pair`/`Sum`); Lens tree 0 real DIRTY | `Lens/ReadingEquiv` (`ReadingEq`/`equivG`/`refinesG`), `Lens/EqPW` (`sameLens` + laws), `Lens/SemanticAtom` (`combine_sym`/universal morphism over `same`), `Universal/QuotLens` (`kernel_eq_E_R`, `recovers_R`, `idempotent_R`), `Theory/Raw/Fold` (`fold_slash_rel`, `fold_slash_iff`) | `theory/lens/{unified_equivalence,dirty_recovery_patterns}`, `research-notes/RFC_reading_equivalence_primitive.md` (+ `G164`), `STRICT_ZERO_AXIOM.md`, `catalogs/correspondence-surface.md` |
| `omega`/`simp` purifications — `Instances.Leaves.DepthJoin` (tier classification), `CayleyDickson.{CayleyHeavy,CDTower}`, `Cauchy.GenericFamily` (pointwise-at-index) all PURE | the modules above; general Nat/`max` helpers in `Meta/Tactic/NatHelper`, Int helpers in `Meta/Int213` | `STRICT_ZERO_AXIOM.md`, `catalogs/correspondence-surface.md` |
| `5²⁵`-as-resolution chain — DELETED (originator); 0.2 ppb α_em result survives on π as literal input | `AlphaEM/GramStructuralCapstone` (5/0), `configCountD`/`configCount 2 = 5²⁵` bare arithmetic | `research-notes/{G156,G157}`, `RERESEARCH_n_u_removal.md` |
| Real-number completeness arc (links 1–13 + depth-arc A–D/B + HolonomicReal φ/e + general generator) | `Lib/Math/Cauchy/{Depth*,Divergence*,EulerDivergenceForm,DepthFloorDetOne,DepthOmegaTower,DepthLiouvilleCoord,DepthPRecursiveInstances,DepthPiQuartic}`, `Meta/Nat/PolyNat`, `Real213/{HolonomicReal,RateModulus,CrossDetOvertake,LiouvilleModulus,CrossDetEqDenom,ReciprocalSeries,CrossDetConstDenom,GeometricThreshold,PresentationDependence,TowerNativeCompleteness,ExpLog/EulerModulus,ExpLog/EulerCertifiedBracket,*}`, `Cauchy/{DepthClosure,DepthCoordGenerator}`, `Analysis/*` | `theory/math/completeness_without_completeness.md` (+ `completeness_relocated`, `analysis/holonomic_modulus`, `analysis/tower_native_completeness`, `probe_twist_conic`); essay `real_without_completeness.md` |
| φ self-similarity (form / count `5^L` / limit-ratio φ) | `SelfSimilarityBridge`, `Real213/{PhiAsCut,PhiConvergence,PhiNormInvariant,PhiAbCut,FibCassiniNat}`, `PellFibCutBridge` | `theory/math/phi_self_similarity.md` |
| The residue / self-covering closure | `Lens/{FlatOntologyClosure,PredicateSelfEncoding}`, `Theory/Raw/{PrimitiveTower,Lambek}` | `research-notes/G152`, `theory/essays/tower_atlas.md` |
| P-orbit closure (P self-defining; every axis sees `{3,2,1}`) | `Mobius213/Px/{CharPolySelf,MobiusSelfForm,ConvergentDet}`, `Theory/Atomicity/OrbitForcing` | `theory/essays/{every_axis_sees_p,p_orbit_closure_master}.md` |
| Repo-wide purity (no Classical/native_decide in 213-math) | `Mobius213/Px/*` (0 dirty) | `STRICT_ZERO_AXIOM.md` |

PURE Nat/Int helper infrastructure (reuse, don't re-derive): `Meta/Nat/NatDiv213`
(`mul_div_self_pure`, `mul_div_cancel_left_pure`, `add_mul_div_left_pure`,
`pow_succ_div`, `add_div_right_pos`, `div_le_self_pos`), `Meta/Nat/PureNat`
(`pow_add`, `mul_assoc`, `add_mul`), `Meta/Tactic/NatHelper` (`succ_sub`,
`add_sub_cancel_right`, `sub_add_cancel`, `add_mul_mod_self_pure`, `le_max_left/right`,
`max_comm`, `two_le_add`, `eq_one_of_add_eq_two`, `max_eq_zero`, `two_le_of_ne_one`,
`ge_two_of_ne_zero_ne_one`, `or_ge_one_of_max_ge_one`), `Meta/Nat/AddMod213`
(`div_le_div_right_pos`, `add_mod_gen`), `Meta/Int213` (`add_nonneg`,
`add_eq_zero_of_nonneg`, `mul_eq_zero`), `Lib/Math/NatRing`
(`nat_mul_assoc`, `nat_add_mul`, `mul_lt_mul_left_pure`).

## Notes / hygiene

  - **Verify Lean SEQUENTIALLY before commit**: `rm <file>.olean` → `lake env lean
    <file>` (exit 0) → `lake build <module>` → `tools/scan_axioms.py <module>`
    (N pure / 0 dirty) → commit.  build-green ≠ purity-green; never trust cached
    "Build completed"; never parallelise build with scan.  **`lake build` (default
    target) does NOT cover every module** (e.g. `Compose.OnLens`) — verify changed
    modules explicitly or with the comprehensive build.
  - **propext-purification playbook** (verified): Lean-core `Nat.{mul_assoc,
    mul_div_cancel_left, add_mul_div_left, add_mul_mod_self_left, add_sub_cancel',
    add_div_right, gcd}` pull `propext` → use the `Meta/Nat` + `NatRing` helpers.
    `omega` is propext-dirty (→ explicit `Nat`/`NatHelper`).  A `simp`/`simpa` that
    *closes* an `Eq`/`Iff` goal pulls `propext` → reduce with `simp only`
    distribute/associate, close with explicit `Iff.intro`/`rw`/`decide`
    (`decide`/`decide_eq_true`/`of_decide_eq_true` PURE; `decide_eq_true_eq` not).
    `funext` = `Quot.sound` → state pointwise (`fold_slash_rel`/`eqPW`/`sameLens`).
  - **Reading-equivalence is the sameness primitive**: when a `=` of views /
    functions / Lenses would pull `funext`/`propext`, state it up to `same`
    (`equivR`/`sameLens`/the codomain's `ReadingEq.same`).  `=` stays only where it
    is axiom-free (concrete codomains) or where it *is* the thesis (`Prop`-atom).
    See `research-notes/RFC_reading_equivalence_primitive.md`.
  - `decide` on `Subtype`/`Raw` equality pulls `propext` via `DecidableEq Raw`;
    use `Tree.noConfusion` (for `a ≠ b`).
  - **Repo-first**: grep + INDEX before coding a "missing" cell.
  - `5²⁵ = N_U = d^(d²)` as a **resolution / universe number is DELETED** — gone,
    not deprecated.  `configCountD`/`configCount 2 = 5²⁵` survive only as bare
    parametric arithmetic; never reintroduce a "the resolution" reading.  Don't use
    "ℝ = final boss" framing.
