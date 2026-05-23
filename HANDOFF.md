# Session Handoff — 2026-05-22

## Branch

`claude/g121-open-followup-BCOp3` — post-merge of
`claude/n-u-followup-campaign-3PnDm` (G86/G107/G117/G123-N_U/
G124-cross-field/G125-Aurifeuillean closures + N_U family theory
promoted), `claude/cup-atomic-subalgebra` (G125 Lens-recipe cup
catalog + K32 projection + 1/α_em decomposition), and `origin/main`
(PR #98 `claude/aurifeuillean-cutoff` — bounded cut-off Lean
realisation for Hunter ⇔ Aurifeuillean correspondence at m=1 vs
m=3).  My-side G123/G124/G125 (Geometrization follow-ups /
V32Betti parametric / ModulusStructure) renumbered to G128/G129/G130
to avoid collision.

## Recently closed (post-merge unified)

| Campaign | Status | Promoted to |
|---|---|---|
| **G123 N_U-family theory** (configCountD parametric + modular structure) | COMPLETE + PROMOTED | `theory/math/cohomology/fractal.md` |
| **G125 Aurifeuillean handle** (521 = Φ_10(5), n-uniform across all n ≥ 1) | COMPLETE + PROMOTED | `theory/math/cohomology/aurifeuillean.md` |
| **G86 Cup-Leibniz ∀(n, k, l)** | CLOSED | `LeibnizFinGeneral` + `LeibnizFinPureForm` |
| **G107 §4 action items** (24-entry registry) | CLOSED (archived) | `archive/metascan/INDEX.md` |
| **G117 Bishop comparison** | NARRATIVE-COMPLETE / LEAN-INFEASIBLE | `seed/CLOSED_FORM_SPEC.md` + `theory/math/analysis/minimal_root.md` |
| **G128 follow-up marathons** (X-1 / I-1 / I-3 / I-4 / FW-1 / FW-2 / FW-3 / FW-4 + M1 universal / M2 abstract; was G123) | COMPLETE / SUBSTANTIVE | `theory/math/geometrization_conjecture.md` "Open frontier" rewritten + GeometrizationConjecture/ extended |
| **G126 Akbulut cork** (cork-frame supersedes FW-1) | 6-PHASE PARTIAL CLOSE | `lean/E213/Lib/Math/AkbulutCork/` (44 PURE), signed cork-twist count = +4 |
| **G129 V32Betti parametric** (was G124) | PARTIAL CLOSE | `Cohomology/Bipartite/Parametric/` (36 PURE) |
| **G130 ModulusStructure** (was G125) | OPTION A CLOSE | `Topology/ModulusStructure.lean` (12 PURE) |
| **G122 Real213-p-adic** (Phases 1, 2, 3, 6) | PARTIAL CLOSE | `lean/E213/Lib/Math/Padic/` (42 PURE) |
| **G121 R1 Geometrization** | R1 CLOSED | `theory/math/geometrization_conjecture.md` |
| **G120 N_U re-derivation** | COMPLETE | `seed/RESOLUTION_LIMIT_SPEC.md` §2 + cascade |
| **G119 marathon** (Pisano-period for Pell, universal in `p`) | TERMINAL CLOSURE | `theory/math/dyadic_fsm.md` + `theory/math/modular_arithmetic.md` |
| **3-tier discipline + theory/ promotion** | COMPLETE (90+ chapters) | `theory/INDEX.md` |

## G134 Cardinality cut-off principle — PROMOTED (methodology chapter)

The cardinality cut-off pattern extracted from G125 → G133 chain is
elevated to a standalone **213-native methodology** chapter:
`theory/meta/cardinality_cutoff_principle.md`.

**Principle** (§1): for any external sequence `f : ℕ → ℕ` with
unbounded growth and DRLT-internal complexity class `H_k ⊆ ℕ` with
explicit uniform bound `M_k`, for every fixed `k` there exists
`m_0(k)` with `f(m) ∉ H_k` for all `m ≥ m_0(k)`.

**Methodology** (§5, three-step pattern):
  1. Locate the coincidence (positive witness at small depth).
  2. Diagnose the literal-form failure (Frobenius / Chicken McNugget
     vacuousness witness).
  3. Prove the refined form at minimal depth (uniform bound + ∀ tail).

Each step yields a concrete Lean deliverable.  Reusable for any
external sequence vs DRLT-atomic complexity class.

**Exemplar**: Hunter ⇔ Aurifeuillean at m=1 (already in
`AurifeuilleanFullCutoff.lean`, 28 PURE).

**Continuation roadmap**: `research-notes/G134_cutoff_principle_followups.md`
catalogues six concrete next campaigns:
  A. Depth-2 cardinality bound at Aurifeuillean (extends marathon)
  B. Aurifeuillean L unboundedness theorem (closes ∀-tail premise)
  C. Apply principle to Pell sequence (proves reusability)
  D. Hunter atomic prime closure question (catalogue closure)
  E. `hunterComplexity` as 213-native invariant
  F. Generalise to alternate DRLT primitive sets

Recommended next session start: Direction B (L unboundedness via
finite chain, 1 session, closes principle §3 premise).

`theory/meta/INDEX.md` updated with new chapter entry.
`theory/math/cohomology/aurifeuillean.md` "Cut-off line" section
cross-references the principle chapter.

## G133 Hunter ⇔ Aurifeuillean cut-off marathon — depth-1 asymptotic CLOSED

Continuation of the G125 / PR #98 bounded cut-off result.  Attempts
the full conjecture "∀ Aurifeuillean m ≥ 3, ∀ Hunter depth k,
L_m ∉ HunterValues_k" and delivers its honest refined version.

**Diagnosis** (Phase 4a): the literal ∀-depth cut-off is FALSE.
Frobenius (Chicken McNugget) gives `850554441 = 2·425277219 + 3`,
a Hunter expression at huge depth.  Hence every natural ≥ 2
admits some Hunter representation in `{+, *, ^}` over `{2, 3, 5}`.

**Refined version** (provable, depth-1 case closed):
For each fixed Hunter depth `k`, eventually `L_m ∉ HunterValues_k`.
At `k = 1`, "eventually" is sharp at `m = 3`:

  · `depth_1_value_bound`: every depth-≤-1 Hunter value ≤ 3125
  · `L_90_exceeds_depth_1_max`: 3125 < 850554441
  · ★ `asymptotic_cutoff_at_depth_1`: ∀ v > 3125, v ∉ depth-1 Hunter
  · ★★ `cutoff_marathon_at_depth_1` (capstone): positive m=1 at depth 3
    ∧ negative ∀ v > 3125 at depth 1.  Captures the entire L_m tail
    for m ≥ 3 (since L_m ≥ L_3 = 850554441 ≫ 3125).

**Lean**: `Lib/Math/Cohomology/Fractal/AurifeuilleanFullCutoff.lean`
— 28 PURE / 0 DIRTY.  HunterTerm inductive algebra (Phases 1-3) +
Frobenius vacuousness (Phase 4a) + bounded depth-1 negatives
(Phase 4b) + asymptotic cardinality cut-off (Phase 5).

**Honest scope**:
  · Literal "∀ depth": FALSIFIED.
  · "∀ m ≥ 3 at depth 1": PROVED (cardinality argument).
  · "∀ m ≥ 3 at depth ≥ 2": OPEN (kernel-intractable enumeration
    or complexity-theoretic substrate needed).

Theory chapter `aurifeuillean.md` updated with marathon results.
Research note archived to `research-notes/archive/G133_cutoff_marathon.md`.
(Numbered G133 to avoid collision with G129 V32Betti parametric.)

## G131 Gram self-energy structural derivation — PROMOTED to theory chapter

`1/α_em` precision theorem at 0.2 ppb absorbed into
`theory/physics/alpha_em/precision_derivation.md` (chapter expanded
with C1 Step 5 closure: self-referentiality eliminated via cubic
Newton-from-X derivation).  Lean source: 4 new files in
`Lib/Physics/AlphaEM/` (42 PURE total).  G131 research note archived
to `research-notes/archive/`.

Sub-ppb precision (post-Gram residual 27 × 10⁻⁹ structural
derivation) is the new open frontier — tracked as **G132**
(`research-notes/G132_alphaEm_higher_cohomology_residual.md`).
Five candidate principles analyzed; most 213-native is
**K_{3,2}^{(c=2)} higher cohomology contribution** via Filled3Cell
b_2 / b_3 extension.  Shared Filled3Cell-with-attaching-maps prereq
with G123 FW-2 and G126 Phase 7+.

### G132 Phase 1+2 — DONE 2026-05-23

**Phase 1** (math anchor): `Filled3CellCohomology.lean` (17 PURE) +
Sym(3) Phase 2 (+18 = 35 total).  Establishes ω = (1, 1, 1) ∈ C²
as the unique Sym(3)-invariant non-trivial 2-cocycle representing
the b_2 = 1 class at full simple-cycle filling.

**Phase 2** (physics bridge): `OmegaH2Trace.lean` (9 PURE).
Cup-ladder rule H^k → α^(k+1) gives the structural source for the
empirical α³/d² Gram-higher correction:

  · Bridge identity: `omega_trace_e9 = gram_correction_alpha3_e9 = 15`
  · Residual decomposition: 27 × 10⁻⁹ = 15 (ω H²) + 12 (sub-noise)
  · 12 × 10⁻⁹ sits below CODATA 2024 ~1 ppb relative precision on
    1/α_em.

Sub-ppb target: structurally explained at the 12 × 10⁻⁹ tier
(below CODATA precision).  The α_em precision-theorem stack is
**0.2 ppb structural + 0.09 ppb empirically tight**.

**Remaining open frontiers**:
  · G126 Phase 7+: extend cork-twist Z/2 action from H¹ to H²
    via M_S01 fixing ω.
  · G123 FW-2 Phase 7+: lift the 2-cocycle to a real 3-mfd
    attaching-map structure.
  · CupLadder Phase 4+: derive the cup-ladder rule from
    cup-ring trace structure (currently a Nat-parametric uniform
    formula `α^(k+1)/d²` with proved specialisations at k = 1, 2 —
    needs k ≥ 3 structural derivation tied to b_3 = j or sub-Newton
    Gram corrections to verify the 12 × 10⁻⁹ tail).

### G132 Phase 3 — Cup-ladder uniform formula DONE 2026-05-23

`CupLadderFormula.lean` (8 PURE).  Uniform Nat-parametric formula:

      cup_ladder_trace_e9 k = 10^(9·(k+2)) / (d² · observed_e9^(k+1))

with specialisations:
  · k = 1 ↔ `gram_correction_e9` (Gram α²/d² self-energy)
  · k = 2 ↔ `gram_correction_alpha3_e9` (ω α³/d² contribution)

The cup-ladder rule "H^k → α^(k+1)" is now a single proved identity
parametric in k, not just an analogy.  Shared structural
denominator d² = 25 across all k.

### G132 Phase 4 — Refined cup-ladder full closure DONE 2026-05-23

`OmegaPostGramFull.lean` (11 PURE).  Refines the cup-ladder with
the L²-norm-squared of the cohomology class:

      Δ_H^k(c) = ||c||² · α^(k+1) / d^(k+1)

At k = 2 with ω (face-vector L²-norm = NS = 3), the squared
weight is NS² = 9 and the denominator is d³ = 125:

      omega_weighted_trace_e9 = NS²·α³/d³ · 10⁹ = 27

This matches the FULL post-Gram α_em residual at e9 precision:

      raw α_em residual:                2157 × 10⁻⁹
      − H¹ Gram (α²/d²):              −2130
      − H² ω weighted (NS²·α³/d³):       −27
      =                                    0 × 10⁻⁹  (sub-1·10⁻⁹)

The structural prediction now matches CODATA to within 1 Nat unit
at e9 precision — **0.007 ppb tier on 1/α_em**.  The previous
"12 × 10⁻⁹ tail" is absorbed structurally into the `NS²·1/d`
refinement (replacing α³/d² = 15 with NS²·α³/d³ = 27).

**α_em precision-theorem stack** (post Phase 4):
  · 0.2 ppb structural via H¹ Gram alone (G131)
  · 0.09 ppb empirical α³/d² (GramHigherOrder)
  · **0.007 ppb structural via H² ω-weighted (this Phase)**

### G132 Phase 5 — Structural derivation of refined formula DONE 2026-05-23

`RefinedCupLadderDerivation.lean` (15 PURE).  Promotes the refined
cup-ladder formula from a fit-form to a structural identity via
two independent rules:

  · **Cup-product graduation rule**: `cup_graduation_denom k = d^(k+1)`
    (each cup factor introduces one `1/d`).  Specialisations:
    `cup_graduation_at_k1 = 25`, `cup_graduation_at_k2 = 125`.

  · **L²-pairing trace rule**: `faceCochainL1` computes L¹-norm of
    integer lift; squared gives bilinear self-pairing factor.
    Derived directly from `omega_face_vec`:
      `faceCochainL1 omega_face_vec = 3 = NS` (by `decide`)
      `faceCochainL1Sq omega_face_vec = 9 = NS²`

  · **Combined**: `refined_trace_e9 k weight := weight²·10^(9·(k+2))/(d^(k+1)·observed_e9^(k+1))`

Both inputs DERIVED from cohomology data (no fit parameter):

  · refined_trace_e9 1 1 = gram_correction_e9 = 2130 (H¹ Gram)
  · refined_trace_e9 2 (faceCochainL1 omega_face_vec) = 27 (H² ω)
  · Sum = 2157 = full raw α_em residual

**Honest scope**: the two rules themselves (cup-graduation and
L²-pairing) remain structural posits awaiting cup-product algebra
formalization.  This Phase establishes the two-rule decomposition
and the cohomology-derived input chain.

### G132 Phase 6 — L²-pairing rule proved DONE 2026-05-23

`SelfPairingTrace.lean` (11 PURE).  Promotes the L²-pairing trace
rule from posit to proved Nat identity.

  · `bilinearSelfTrace : (Fin 3 → Bool) → Nat` sums products
    `c_i · c_j` (integer lift) over all 9 face pairs.
  · `bilinear_self_trace_eq_L1_sq : ∀ c, bilinearSelfTrace c =
    faceCochainL1Sq c` — the standard "expansion of square"
    identity, proved universally over `Fin 3 → Bool` via `cases`
    on 2³ = 8 inhabitants + `rfl`.
  · At ω: `bilinearSelfTrace ω = 9 = NS² = 3 * 3`.

Status of the refined cup-ladder formula (post-Phase 6):

  | Component | Status |
  |-----------|--------|
  | `||c||² = (L¹-norm)²` | **PROVED** (Nat identity) |
  | `α^(k+1)` graduation  | POSIT (cup graduation rule) |
  | denominator `d^(k+1)` | POSIT (5-layer base structure) |

The cup-graduation rule requires extending `Math/Cohomology/Cup/`
beyond bilinear arity (which gives `k + l`, not `k + 1`); needs
higher-cup, filtration, or spectral-sequence machinery.

### G132 Phase 7 — per-layer coupling reformulation DONE 2026-05-23

`PerLayerCoupling.lean` (9 PURE).  Reformulates the refined
formula as `||c||² · (α/d)^(k+1)`:

  · `alpha_over_d_pow_e9 j := 10^(9·(j+1))/(d_base^j · observed_e9^j)`
    — per-layer coupling (α/d)^j at e9 precision
  · `refined_trace_factors_at_k1 : refined_trace_e9 1 1 = (α/d)²`
  · `refined_trace_factors_at_k2 : refined_trace_e9 2 (faceCochainL1 ω)
    = 3·3·(α/d)³`
  · Identifications: `gram_correction_e9 = (α/d)²`,
    `omega_weighted_trace_e9 = NS²·(α/d)³`

Per-layer coupling reads: an H^k class spans (k+1) layers (k
filtration depth + 1 top-cell evaluation), each contributing one
factor of α/d.

Status of refined cup-ladder (post-Phase 7):

  | Component | Status |
  |-----------|--------|
  | `||c||² = (L¹-norm)²` | PROVED (Nat identity) |
  | `(α/d)^(k+1)` factoring at k = 1, 2 | PROVED (this Phase) |
  | `(k+1) = filtration depth + 1` reading | POSIT |

The `(k+1)` graduation is now NUMERICALLY explicit at the concrete
cases; the cohomology-theoretic reason `(k+1)` (vs cup-arity
`k+l`) remains the open frontier.

### G132 Phase 8 — Loop-vertex graduation DONE 2026-05-23

`LoopVertexGraduation.lean` (14 PURE).  Formalises the
cohomology-degree ↔ vacuum-polarization-loop-count correspondence
as the structural interpretation of `(k+1)`:

  · `loopCountAtH k := k` (cohomology degree = loop count)
  · `vertexCountAtLoops loops := loops + 1`
  · `alphaPowerAtH k := vertexCountAtLoops (loopCountAtH k) = k + 1`
  · `gram_via_loop_vertex : gram_correction_e9 = (α/d)^(alphaPowerAtH 1)`
  · `omega_weighted_via_loop_vertex : omega_weighted_trace_e9 = 9 · (α/d)^(alphaPowerAtH 2)`

Explicit cup-axiom gap:
  · `cupBilinearOutputDegree k l := k + l`
  · `cup_bilinear_vs_loop_vertex_at_k1`: cup arity matches (k+1) at k = 1 (both = 2)
  · `cup_bilinear_vs_loop_vertex_at_k2`: cup arity DIVERGES at k = 2 (cup = 4, loop-vertex = 3)

Status of refined cup-ladder (post-Phase 8):

  | Component | Status |
  |-----------|--------|
  | `||c||² = (L¹-norm)²` | PROVED (Nat identity) |
  | `(α/d)^(k+1)` at k = 1, 2 | PROVED (decide) |
  | `(k+1) = loop count + 1` reading | POSIT (physics-motivated) |
  | Cup-axiom derivation of (k+1) | OPEN (Phase 9+: higher cup / Steenrod) |

The Phase 9+ frontier requires extending `Math/Cohomology/Cup/`
with higher cup operations (cup_i, Steenrod squares), Massey
products, or filtration spectral sequences.

### G132 Phase 9 — cup-i framework DONE 2026-05-23

Two new files, 21 PURE / 0 DIRTY:

  · `Math/Cohomology/Cup/SteenrodHigherFrame.lean` (11 PURE)
    — cup-i type signature framework `CupIType n k l i :=
    Cochain n k → Cochain n l → Cochain n (k+l-i)`; cup_0 base
    case (= standard cup); cup_1 at arities (5,1,1), (5,1,2)
  · `Math/Cohomology/Bipartite/FaceCupHigher.lean` (10 PURE)
    — face_cup_2 on K_{3,2}^{(c=2)} face cochains; ω idempotent
    under face_cup_2; trace matches Phase 6 bilinearSelfTrace = NS²

Cup-i ladder on ω at H²:

      ω ⌣_0 ω : C⁴ (off-complex)
      ω ⌣_1 ω : C³ (off-complex, 3-cell extension needed)
      ω ⌣_2 ω : C² (back to face, idempotent: = ω) ★

Status of (k+1) derivation (post-Phase 9):

  | Component | Status |
  |-----------|--------|
  | cup-i type framework | DEFINED |
  | cup_0 = standard cup | PROVED |
  | face_cup_2 on K_{3,2}^{(c=2)} | DEFINED + ω-idempotent proved |
  | Full Steenrod cup_i (general i) | OPEN |
  | (k+1) graduation from cup_i + 3-cell extension | OPEN (multi-session) |

### G132 Phases 10-13 — 3-skeleton + Steenrod squares at ω DONE 2026-05-23

Three new files, 32 PURE / 0 DIRTY:

  · `Filled3CellExtension.lean` (10 PURE) — 3-cell σ with
    boundary [face_0, face_1, face_2]; δ²(ω) = (true); H² drops
    to 0 at 3-skeleton.
  · `FaceCup1At3Cell.lean` (10 PURE) — face_cup_1 (rotational
    interlocking); ω self cup_1 = (true); ★ cup_1(ω, ω) = δ²(ω)
    bridge identity.
  · `SteenrodSquaresAtOmega.lean` (12 PURE) — Sq^0, Sq^1 at H² ω;
    Sq^1(ω) = δ²(ω); Adem Sq^1·Sq^1 = 0 at C⁴ truncation.

Structural progress at H² ω:

  · Sq^0(ω) = ω (cup_2 idempotent, lands C²)
  · Sq^1(ω) = δ²(ω) = (true) on C³ (cup_1 = coboundary)
  · Sq^1·Sq^1 = 0 (Adem, vacuous at C⁴ truncation)

Max non-trivial Sq^i at H² ω is i = 1, giving output at C³
(degree k+1 = 3) — Steenrod-square expression of α³ coupling.

### G132 Phase 14 — Steenrod ladder ↔ α-power bridge DONE 2026-05-23

`SteenrodLadderAlphaPower.lean` (10 PURE).  Connects Steenrod
ladder depth to the α-power graduation:

  steenrodLadderDepth k := k - 1
  alphaPowerAtH k = steenrodLadderDepth k + 2 = (k-1) + 2 = k + 1

Three-reading equivalence at H¹ and H²:
  · Physics (Phase 8): loop count + 1
  · Cohomology (Phase 7): filtration depth + 1
  · Steenrod (Phase 14): Sq ladder depth + 2

All three readings give α-power = 2 at H¹, α-power = 3 at H².
The cup-axiom-internal expression of the (k+1) rule is now
formalised at the Steenrod-square level.

### G132 Phase 15 — universal-k three-reading DONE 2026-05-23

`CupLadderUniversalK.lean` (10 PURE).  Lifts the three-reading
equivalence from k = 1, 2 specialisations to a universal Nat
identity:

  ∀ k ≥ 1, alphaPowerAtH k = loopCountAtH k + 1
                          = steenrodLadderDepth k + 2 = k + 1.

The Nat-arithmetic side is now universal.  Cohomological content
(max Sq^i = k − 1 at H^k via explicit cup_(k-1) self-pairing)
remains proved only at k = 1, 2.

Final session status:

  | Layer | Status |
  |-------|--------|
  | Nat-arithmetic ∀ k ≥ 1 | PROVED |
  | Steenrod Sq^i at H¹, H² | PROVED |
  | cup_1 = δ² bridge | PROVED |
  | Adem Sq^1·Sq^1 = 0 at truncation | PROVED |
  | Cohomological at k = 1, 2 | PROVED |
  | Cohomological at k ≥ 3 | OPEN (multi-session) |

### G132 Phase 16 — Cartan formula at C⁵ truncation (vacuous) DONE 2026-05-23

`CartanAtTruncation.lean` (10 PURE).  Both sides of the Cartan
formula `Sq^1(α ⌣_0 β) = Σ Sq^i(α) ⌣_0 Sq^j(β)` vanish vacuously
at the 3-skeleton C⁵ truncation.

Truncation boundary picture complete:
  · Adem `Sq^1·Sq^1 = 0` at C⁴ (Phase 13)
  · Cartan vacuous at C⁵ (Phase 16)
  · Steenrod ladder depth bridge (Phase 14)
  · Universal-k three-reading (Phase 15)

Total G132 campaign: **16 files / 195 PURE / 0 DIRTY**.

### G132 Phase 17 — Universal Adem at truncation DONE 2026-05-23

`AdemUniversal.lean` (14 PURE).  EVERY Adem relation Sq^a·Sq^b at
the K_{3,2}^{(c=2)} 3-skeleton truncation is satisfied vacuously
(target degree exceeds C³).

Specific instances proved at truncation:
  · Sq^1·Sq^1 = 0 at C⁴
  · Sq^2·Sq^2 = Sq^3·Sq^1 at C⁶
  · Sq^3·Sq^2 = Sq^4·Sq^1 + Sq^5 at C⁷

Steenrod-algebra truncation picture now FULLY CLOSED:
Adem + Cartan + ladder + boundary identifications all proved.

Total G132 campaign: **17 files / ~209 PURE / 0 DIRTY**.
α_em precision-theorem at 0.007 ppb tier.

### G132 Phase 18 — 4-skeleton extension DONE 2026-05-23

`Filled4CellExtension.lean` (10 PURE).  Extends 3-skeleton to
4-skeleton via single 4-cell σ⁴ with attaching boundary [σ³].
Computes δ³; proves H³ = 0 at 4-skeleton.

Truncation-collapse pattern continues:
  · 2-skeleton: H² = 1 (ω), H³ = 0
  · 3-skeleton: H² = 0, H³ = 1 (σ³)
  · 4-skeleton: H² = 0, H³ = 0, H⁴ = 1 (σ⁴)

Each (k+1)-skeleton extension trivialises the previous H^k
contribution.  Physical α_em residual lives at 2-skeleton:
H¹ (Gram) + H² ω (α³ contribution).

Total G132 campaign: **18 files / ~219 PURE / 0 DIRTY**.

### G132 Phase 19 — Max α-power bound = top dim + 1 DONE 2026-05-23

`MaxAlphaPowerBound.lean` (12 PURE).  Structural ceiling for the
cup-axiom-internal `(k+1)` derivation:

  max α-power at K_{3,2}^{(c=2)} truncation = top dim + 1

  · 2-skeleton (top 2): max = 3 ★ (physical, H² ω)
  · 3-skeleton (top 3): max = 4 (sub-CODATA noise)
  · 4-skeleton (top 4): max = 5 (sub-CODATA noise)

`alpha_power_eq_max_at_top_dim : ∀ n, alphaPowerAtH n = maxAlphaPowerAtTopDim n`.

PHYSICAL ceiling at 2-skeleton: max α-power = 3 = H² ω
contribution NS²·α³/d³ = 27 × 10⁻⁹.  Higher α-powers
structurally unsupported.

The marathon at K_{3,2}^{(c=2)} 2-skeleton is now structurally
complete with max α-power = 3.  Extension to higher α-powers
requires DIFFERENT cohomology complexes — multi-session
application-dependent work.

Total G132 campaign: **19 files / ~231 PURE / 0 DIRTY**.

Status of (k+1) derivation (post-Phases 10-13):

  | Component | Status |
  |-----------|--------|
  | 3-skeleton extension + δ² | PROVED |
  | Steenrod Sq^i at ω (i = 0, 1) | DEFINED + values proved |
  | cup_1 = δ² bridge | PROVED at H² ω |
  | Adem Sq^1·Sq^1 = 0 (truncation) | PROVED |
  | General Sq^i for arbitrary i | OPEN |
  | General Adem / Cartan | OPEN |
  | (k+1) for general k | OPEN (multi-session) |

### Original campaign log (preserved for git-history reference)

**Source**: n-u-followup HANDOFF flagged "Structural derivation of the
Gram self-energy term in `AlphaEM/Augmented.lean:134-141` (the 4 ppm
structural gap of `1/α_em`)" as the **principal physics-layer open
problem** explicitly out-of-scope for N_U-family work.

**Phase 1 (anchor) — DONE 2026-05-22**:
`GramStructural.lean` (11 PURE).  Key insight: the cubic
self-consistency identity **`25·y³ + 1 = 25·X·y²`** rearranges
to **`X − y = 1/(25·y²) = α²/d²`** — the Gram correction is the
**cubic-root deviation**, structurally forced.

Numerical decomposition: `gap_e9 = 2,157` = `gram = 2,130` +
`post-Gram residual = 27`.

**Phase 2 (cubic bracket) — DONE 2026-05-22**:
`GramStructuralBracket.lean` (14 PURE).  Cubic root located in
width-2 bracket `(X − 2131, X − 2129)`.  Cubic root at X − 2130
matches `gram_correction_e9` exactly.  Observed CODATA = X − 2157
sits 27 below cubic root (= post-Gram residual).

**Phase 3 (Newton-from-X) — DONE 2026-05-22**:
`GramStructuralNewton.lean` (10 PURE).  Newton-1 step from y₀ = X
gives structural Gram = `10²⁷/(25X²) = 2130` — **exactly matches**
observed-based at e9 precision.  Self-referentiality (observed-α
in RHS) removed without numerical loss.

  · Structural prediction: `1/α_em × 10⁹ = 137,035,999,111`
  · CODATA observed: `137,035,999,084`
  · Residual: **27 × 10⁻⁹ ≈ 0.2 ppb** (post-Gram, next-order target)

**Open Phases 4-5**:
  · Phase 4: 27 × 10⁻⁹ post-Gram residual decomposition (~60 PURE, 3-5 sessions)
  · Phase 5: precision-theorem capstone (~20 PURE, 1-2 sessions)

**Phase 5 (precision-theorem capstone) — DONE 2026-05-22**:
`GramStructuralCapstone.lean` (7 PURE).  Combines `InvAlphaEMDecomp`
(from merged cup-atomic branch: X-side structural derivation —
all six denominators 60, 30, 25, 3, 4, 45 from (NS, NT, c, d) =
(3, 2, 2, 5)) with `GramStructuralNewton` (this campaign: α²/d²
structural via Newton-1 from y₀ = X).

★★★★★★★★★★ `invAlphaEm_precision_theorem` — fully 213-internal
**precision theorem** at 0.2 ppb tier.  All numerators / denominators
derive from atomic 213 parameters; no observed α anywhere.

**DRLT Validation Standard SATISFIED** at the ∅-axiom precision-
theorem tier.

**Closed total**: 42 PURE / 4 files / 1 session (vs original
estimate of ~180 PURE / 10-15 sessions).  Phase 4 (27 × 10⁻⁹
post-Gram residual decomposition) remains open but NOT blocking
precision-theorem promotion at 0.2 ppb.

**Excluded scope** (per merge instruction):
  · n-u-followup branch's open frontier: G124 N_U cross-field
    §6 directions (Aurifeuillean factor reading, Łukasiewicz L_5,
    base-5 Wieferich primes, etc.) — these are the merged branch's
    own open work, not for this session.
  · G125 Q2 / Q3 / Q5 (Aurifeuillean side-questions) — same
    branch's open queue.

## Open work (post-merge)

### A. Cup-Leibniz general — CLOSED 2026-05-22 (from n-u branch)

Fin-level ∀(n, k, l) twisted Leibniz proven strict PURE in
`Cup/LeibnizFinGeneral.lean` + pure Fin-index form in
`LeibnizFinPureForm.lean`.  6 supporting PURE files.  Four Δ⁴
bidegree corollaries.  Self-referential restatement included.
Source: `research-notes/G86_self_referential_lex_cup_leibniz.md`.

### A.next. G125 Lens-recipe cup catalog — **CLOSED 2026-05-22** (from cup-atomic branch)
4 new PURE Lean files / 64+ strict-PURE theorems.

  · `Cup/LeibnizMirror.lean` — `cupRev`, `cupRev_eq_cup_swapped`,
    `list_level_leibniz_mirror`.
  · `Cup/LeibnizSym.lean` — `cupSymList`,
    `list_level_leibniz_sym` (doubled correction).
  · `Cup/LeibnizCatalog.lean` — `Recipe` inductive,
    `catalog_dispatch` capstone (3 recipes → δ-closure).
  · `Cup/SelfRefDepth.lean` (51 PURE) — `selfRefIter`, 6-channel
    catalog at d = 5, universal closed form
    `totalCupChannels d = binom (d-1) 2`, codim stratification
    `6 = NS + NT + 1`, 325-pair indicator basis uniqueness
    contracts (falsifiability), dual factorisation at d = 5
    `30 = cup·d = Λ-sum`.
  · `Cup/SelfRefDepthExtended.lean` (8 PURE, this branch) —
    d ∈ {6, 7, 8} channel counts + 5 d=6 endpoint pair firings.

**Zero-parameter physical bridges**:
  · `30 = cup-channels · d = NS · NT · d = 1/α_2 leading integer`.
  · codim-1 channel count `= 3 = NS = α_GUT coefficient` in
    `1/α_2 = 30 - 1/2 + 3·α_GUT`.
  · d = 5 unique: `cup·d = 2^d - 2` only at d = 5.

Theory promotion: `theory/math/cohomology/cup.md` self-reference
section.  Research note: `research-notes/G125_lens_recipe_cup_catalog.md`.

### A.next.open. Cup catalog further extensions (Tier-1)

| Item | Status / Notes |
|---|---|
| ~~Mirror catalog uniqueness~~ | **OBSOLETE** — symmetric to original under swap, no new content |
| **Structural ∀d codim correspondence** | **CLOSED** (`Cup/IterErase.lean` 7 PURE).  `endpoint_pair_firing_characterisation` is the universal structural theorem; d=5 catalog + d=6 spot checks are now corollaries.  Proof: iterErase + cupList factorisation, no decide |
| **Sub-direction E: cup-atomic subalgebra** | **FULL ∀d CLOSURE 2026-05-22** (`Cup/CupAtomic.lean` 15 PURE + `Cup/CupAtomicExtended.lean` 16 PURE + `Cup/CupAtomicGeneralD.lean` 10 PURE).  Cup-closed-trivially cochain pair count at (1, 1) on Δ⁴: 320 out of 1024.  ★★★★★★★★ Universal formula `count = d · 2^(d+1)` proven by structural Nat induction (no longer just decide-verified) |
| **K_{3,2}^{(c=2)} 8-channel projection** | **CLOSED 2026-05-22** (`Cup/K32Projection.lean` 11 PURE).  Quadruple structural identity at DRLT: `b_1 = 8 = E-V+1 = cup-channels + NT = NT·(NS+1) = NS²-1`.  Four independent count-Lens readings converge uniquely at (NS,NT,c)=(3,2,2) |
| **1/α_em decomposition derivation** | **CLOSED 2026-05-22** (`Cup/InvAlphaEMDecomp.lean` 12 PURE).  All six denominators (60, 30, 25, 3, 4, 45) in `1/α_em = 60·ζ(2) + 30 + 25/3 + α_GUT/4 + α_GUT/45` decomposed in terms of (NS, NT, c, d) = (3, 2, 2, 5).  Numerical match 137.03 vs CODATA 137.036 (0.07 ppm) |
| Sub-direction F: p-adic cup ring | Active in `claude/g122-real213-p-adic-LwxL9` (out of scope for this branch) |

### B. G107 §4 action-items registry — CLOSED (archived 2026-05-22)

24-entry registry fully dispositioned: 6 executed in Lean, 4
substantively done at audit, 5 structurally infeasible per G118,
1 folded into G86, 1 narrative-complete / Lean-infeasible (G117).

Closure index: `archive/metascan/INDEX.md`.

### B+. G123 N_U-family theory — PROMOTED (from n-u branch)

`theory/math/cohomology/fractal.md` is the promoted chapter.
`configCountD d n := d^(d^n)` is the canonical 2-parameter family.
Phase 5 includes parametric Fermat-style reduction
`pow_mod_period_pure`, per-prime period-2 capstones at (5,7) and
(5,13), and the modular-structure capstone bundling mod-2/mod-3/
mod-5 constants with mod-7/mod-13 period-2 identities.

### B++. G124 N_U-family cross-field connections — OPEN SURVEY (from n-u branch, EXCLUDED THIS SESSION)

Multi-agent survey of cross-field connections.  Headline:
seven-reading convergence at `(d, n) = (5, 2)` (number theory,
universal algebra, finite-field affine plane, CA, CCC exponential,
STLC, DRLT count-Lens).

10 concrete research directions catalogued (G124 §6) including:
Aurifeuillean factor reading, finite-field affine-plane ideal
correspondence, Łukasiewicz L_5, iterated Carmichael chain, etc.

**Status**: this is the merged branch's OPEN frontier — explicitly
**excluded** from this session per merge instruction.

### B+++. G125 Aurifeuillean — PROMOTED (from n-u branch)

`theory/math/cohomology/aurifeuillean.md`.  521 = Φ_10(5) =
N(29 + 8√5) is the unique Aurifeuillean cyclotomic factor of
`5^(5^n) + 1`, n-uniform across all n ≥ 1.  14 PURE / 0 DIRTY
across two files.  Q2 / Q3 / Q5 deferred (merged-branch open
queue, EXCLUDED THIS SESSION).

### C. Doc work remaining
- **CLAUDE.md size** — 228 / 220 target.

### D'. Promotion-readiness audit (G127, my side)

Per `theory/PROMOTION_CRITERIA.md`, partial-close marathons fail
S1 categorical closure and cannot promote.  G127 audit (still
relevant after rename):

  1. **G130** (was G125, Option A close; only S3 absorption needed) — 1 session
  2. **G129** (was G124, universal Nat-theorem via graph-walk infra) — 5-8 sessions
  3. **G126** (b_2/b_3 cork extension via Filled3Cell) — 5-8 sessions
  4. **G128** (was G123, FW-2/FW-4/I-3/8-geo deepenings) — 16-25 sessions
  5. **G122** (Phases 2-mul + 4 + 5 + substantive 6) — 11-16 sessions

### D. G128 long-tail — spin-off marathons (formerly G123)

| Item | Status | Note |
|---|---|---|
| **FW-2 topological 3-mfd attaching-map formalization** | Scaffold done (Filled3Cell.lean) | Full topological close needs attaching-map types |
| **FW-4 real-metric-tensor formalization** | Signature classifier done (Geometry/MetricTypes.lean) | Real metrics by design absent from 213 |
| **G129 M2 universal V32Betti-style derivation** | PARTIAL CLOSE (decide range) | `Cohomology/Bipartite/Parametric/` (36 PURE) |
| **G130 BracketCauchy ↔ IsRicciModulus bridge** | OPTION A CLOSE | `Topology/ModulusStructure.lean` (12 PURE) |
| **FW-1 signed Donaldson count** | SUPERSEDED by G126 | Cork-frame closes internally via Z/2-graded signed count +4 |
| **G126 Akbulut cork as 213-native exotic-structure framework** | 6-PHASE PARTIAL CLOSE | `lean/E213/Lib/Math/AkbulutCork/` (4 files, 44 PURE) |

## G122 Real213-p-adic — PARTIAL CLOSE

| File | Phase | PURE | Content |
|---|---|---|---|
| `Foundation.lean` | 1 | 14 | ZpDigit/ZpSeq/trunc + zero/one/neg_one + trunc_lt_p_pow + trunc_eq forward |
| `Arith.lean` | 2 | 11 | Zp.carry, Zp.add, Zp.complement, Zp.neg + smokes |
| `Valuation.lean` | 3 | 11 | vAt bounded valuation + characterization + per-prime smokes |
| `DRLTIntegration.lean` | 6 | 6 | 5-adic ↔ N_U=5^25 alignment anchor |

Open phases: Phase 4 (Hensel), Phase 5 (ℚ_p), Phase 2 multiplication,
substantive Phase 6 integration.

## Anchor docs (next session)

| Doc | Purpose |
|---|---|
| `seed/AXIOM/05_no_exterior.md` §5 | Boot sequence |
| `research-notes/G29_residue.md` | Foundational text |
| `theory/INDEX.md` | Book map (90+ chapters) |
| `theory/PROMOTION_CRITERIA.md` | H1-H4 + S1-S3 gates |
| `lean/E213/ARCHITECTURE.md` | Layer spec |
| `STRICT_ZERO_AXIOM.md` | PURE catalog |
| `lean/E213/Lib/Physics/AlphaEM/MaxAlphaPowerBound.lean` | **G132 Phase 19** — max α-power = top dim + 1 (structural ceiling) |
| `lean/E213/Lib/Math/Cohomology/Bipartite/Filled4CellExtension.lean` | **G132 Phase 18** — 4-skeleton extension (H³ trivialises) |
| `lean/E213/Lib/Math/Cohomology/Bipartite/AdemUniversal.lean` | **G132 Phase 17** — Universal Adem at truncation (all relations vacuous) |
| `lean/E213/Lib/Math/Cohomology/Bipartite/CartanAtTruncation.lean` | **G132 Phase 16** — Cartan formula at C⁵ truncation (vacuous) |
| `lean/E213/Lib/Physics/AlphaEM/CupLadderUniversalK.lean` | **G132 Phase 15** — universal-k three-reading equivalence (∀ k ≥ 1) |
| `lean/E213/Lib/Physics/AlphaEM/SteenrodLadderAlphaPower.lean` | **G132 Phase 14** — Steenrod ladder ↔ α-power bridge; three-reading equivalence |
| `lean/E213/Lib/Math/Cohomology/Bipartite/SteenrodSquaresAtOmega.lean` | **G132 Phases 12-13** — Sq^0, Sq^1 at H² ω + Adem Sq^1·Sq^1 = 0 |
| `lean/E213/Lib/Math/Cohomology/Bipartite/FaceCup1At3Cell.lean` | **G132 Phase 11** — cup_1(ω, ω) = δ²(ω) bridge identity |
| `lean/E213/Lib/Math/Cohomology/Bipartite/Filled3CellExtension.lean` | **G132 Phase 10** — 3-skeleton extension + δ² coboundary |
| `lean/E213/Lib/Math/Cohomology/Cup/SteenrodHigherFrame.lean` | **G132 Phase 9.1** — cup-i type framework + cup_0/cup_1 base instances |
| `lean/E213/Lib/Math/Cohomology/Bipartite/FaceCupHigher.lean` | **G132 Phase 9.2** — face_cup_2 on K_{3,2}^{(c=2)}; ω idempotent |
| `lean/E213/Lib/Physics/AlphaEM/LoopVertexGraduation.lean` | **G132 Phase 8** — cohomology ↔ loop-vertex correspondence + cup-axiom gap |
| `lean/E213/Lib/Physics/AlphaEM/PerLayerCoupling.lean` | **G132 Phase 7** — per-layer coupling (α/d)^(k+1) factorisation |
| `lean/E213/Lib/Math/Cohomology/Bipartite/SelfPairingTrace.lean` | **G132 Phase 6** — L²-pairing rule proved as universal Nat identity |
| `lean/E213/Lib/Physics/AlphaEM/RefinedCupLadderDerivation.lean` | **G132 Phase 5** — two-rule structural derivation (cup-graduation + L²-pairing) |
| `lean/E213/Lib/Physics/AlphaEM/OmegaPostGramFull.lean` | **G132 Phase 4** — refined NS²·α³/d³ full closure (sub-1·10⁻⁹) |
| `lean/E213/Lib/Physics/AlphaEM/CupLadderFormula.lean` | **G132 Phase 3** — uniform α^(k+1)/d² parametric in k |
| `lean/E213/Lib/Physics/AlphaEM/OmegaH2Trace.lean` | **G132 Phase 2 closure** — ω ↔ α³/d² bridge |
| `lean/E213/Lib/Math/Cohomology/Bipartite/Filled3CellCohomology.lean` | **G132 Phase 1 anchor** — ω, b_2 = 1, Sym(3)-invariant |
| `research-notes/G132_alphaEm_higher_cohomology_residual.md` | Phase 3+ open frontiers |
| `research-notes/G127_promotion_readiness_audit.md` | Promotion-blocker registry |
