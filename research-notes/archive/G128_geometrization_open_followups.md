# G128 — Geometrization open follow-ups registry

**Date**: 2026-05-22
**Branch**: `claude/g121-open-followup-BCOp3`
**Purpose**: single authoritative list of every actionable item left
open by G121 (the Geometrization R1 close + R1+ partials).
Companion to `G107_action_items_registry.md` (G90-G106 items) — same
shape, narrower scope.

Sources:
  · `research-notes/G121_dim4_self_pointing_axis.md` §6 + §FW + R1+ tail
  · `theory/math/geometrization_conjecture.md` "Open frontier"
  · `lean/E213/Lib/Math/GeometrizationConjecture/INDEX.md` marathon table
  · `HANDOFF.md` 2026-05-22 closure log

R1 itself is **CLOSED** at 149 PURE / 0 DIRTY across 25 steps; this
registry covers only what remains after promotion of R1 to
`theory/math/geometrization_conjecture.md` and after the three
R1+ files (`Generalization`, `JsjDeep`, `MetricGeometries`) landed.

---

## §0.  Numbering note — G122 collision

G121's own `§FW` registry (step 25, commit `5d4137b0`) tagged its
four marathon candidates **G122 / G128 / G129 / G130**.  Between
G121's close and this registry, branch
`claude/lean4-ast-patterns-g1gWN` merged and claimed **G122** for
the Real213-p-adic campaign (per `HANDOFF.md` "Next campaign").
The G121-internal labels are therefore stale:

| G121 §FW label | G121-internal topic            | Post-renumber name used in this registry |
|---|---|---|
| ex-G122 | 4-mfd exotic enum via Sym(3) gauge | **FW-1**  (marathon, unnumbered until launch) |
| ex-G128 | JSJ deeper close (3-cell complex)  | **FW-2**  (partial via `JsjDeep.lean`) |
| ex-G129 | K_{NS,NT}^{(c)} chartBase ≥ 9      | **FW-3**  (partial via `Generalization.lean`) |
| ex-G130 | E³/H³/H²×ℝ direct realization      | **FW-4**  (partial via `MetricGeometries.lean`) |

`theory/math/geometrization_conjecture.md` already silently
relabeled these as "Real213-p-adic extensions A/B/C"; this file
makes the rename explicit.  When any of FW-1..FW-4 actually
launches as a marathon, it picks the next chronological G-number
at that time — **don't pre-allocate**.

---

## §1.  Open items — ordered by readiness

### FW-1 — 4-mfd exotic enumeration via Sym(3) gauge  [SUBSTANTIVE COUNT ✓]

**Trigger**: user 2026-05-22 (G121 step 25): "4차원을 좌절할 게
아니라 가장 투명하게 잘 보여주는 거였던건데… 그 엑조틱 자체를
조사해봣으면 달랐을지두".

**Goal**: an explicit 213-native counting theorem for exotic smooth
structures on closed 4-manifolds, derived from K_{3,2}^{(c=2)} gauge
data (Sym(3) action, |Aut(K)| = 768, gluon-octet coker(ι*)).

**Substantive count added 2026-05-22** (`Exotic4Mfd.lean`):
  · `sym3GaugeInvariant : Nat := Sym3IrrepDecomp.fixedSize` (= 4)
    — atomic 213-native gauge invariant.
  · **Per-element Sym(3) fix counts** (Burnside prerequisites):
    `fixedSizeS01 = 32`, `fixedSizeS12 = 32`, `fixedSizeRho = 4`
    (decide-verified via 256-cochain enumeration).
  · **`sym3OrbitCount = 60`** — the Burnside-derived count of
    distinct Sym(3)-orbits on H¹(K_{3,2}^{(c=2)}).  Formula:
    `(256 + 3·32 + 2·4) / 6 = 360 / 6 = 60`.
  · `sym3_burnside_sum` — Burnside identity verified at the
    instance level: `256 + 3·fixedSizeS01 + 2·fixedSizeRho =
    sym3OrbitCount · 6`.
  · `fw1_substantive_sym3_orbit_count` — 8-conjunct capstone
    bundling the substantive count + decomposition (4 singleton
    orbits + 56 non-singleton orbits = 60 total).

This is the **213-native gauge-orbit count** playing the
structural role of Donaldson's integer instanton-moduli
enumeration: 60 distinct Sym(3)-gauge-equivalence classes of
cochains, of which 4 are gauge-invariant (singletons) and 56 are
non-trivial gauge orbits (sizes 2, 3, or 6 by stabilizer subgroup).

**Sub-orbit decomposition added 2026-05-22**:
  · `M_S02` explicit matrix (= `M_S01 · M_S12 · M_S01`) with
    involution verification `M_S02_squared_pointwise`.
  · `fixedSizeS02 = 32` (third transposition, decide-verified).
  · `transpFixedCount = 88` via inclusion-exclusion `3·32 − 3·4 + 4`.
  · **Sub-orbit decomposition `(4, 0, 28, 28)`**:
      - 4 orbits of size 1 (Sym(3)-fixed singletons)
      - 0 orbits of size 2 (no cochain has stab = A_3 since
        `|Fix(ρ)| = |Fix(Sym(3))| = 4`)
      - 28 orbits of size 3 (stab = ⟨transposition⟩)
      - 28 orbits of size 6 (trivial stab)
  · `fw1_suborbit_decomposition` capstone (8-conjunct bundle).

**Still missing** (full Donaldson-comparison close):
  · Signed counting: Donaldson invariants are signed sums; the
    213-native sign assignment from K-deployment data is open.
  · Standard-math interface for "smooth structure equivalence"
    on a topological 4-manifold — 213 doesn't have this by design;
    comparison requires an external bridge.

**Effort spent**: ~1 session.  Substantive enumeration achieved;
remaining 4-10 sessions for full Donaldson comparison.

**Falsifier potential**: HIGH.  `sym3OrbitCount = 60` is a concrete
prediction.  Any standard-math 4-mfd whose Donaldson invariant
disagrees with this 213-derived count would falsify the
Sym(3)-gauge ↔ exotic-smooth correspondence.

---

### FW-2 — JSJ deeper close (3-cell complex)  [PARTIAL DEEPENED]

**Current state**: `JsjDeep.lean` (~20 PURE) — χ-target scaffold +
3-mfd catalog + bipartite S/T cut canonical decomposition.

Deepening added 2026-05-22:
  · 3-mfd Euler-target catalog: S³, T³, L(p,q), connected sums
    all unified at χ = 0 (`closed_3mfd_euler_unified`).
  · K_{3,2}^{(c=2)} cell-complex (k, j) parameter family realizing
    closed 3-mfd targets (`K32_cell_complex_3mfd_parameter_family`).
  · Bipartite S/T cut as canonical decomposition: S-side, T-side,
    sum-to-chartBase, non-triviality at K_{3,2} formalized.
  · `JSJ_deeper_consolidation` capstone bundling all of the above.

**3-cell infrastructure added 2026-05-22** (`Filled3Cell.lean`,
21 PURE):
  · `Cell3ComplexK32` structure (k 2-cells + j 3-cells)
  · `chi` Euler-characteristic computation (5 − 12 + k − j)
  · `realizesClosed3Mfd` predicate (k − j = 7)
  · Specific 3-mfd realizations: (7,0), (8,1), (9,2), (10,3) all χ=0
  · Naive Betti-number computations (b₀ = 1, b₂ = k − j, b₃ = j)
  · Filling chain χ values for k ∈ [0,3]: −7, −6, −5, −4
  · `cell3_extension_scaffold` capstone (10-conjunct)
  · Bridge in `JsjDeep.lean`:
    `chi_K32_extended_eq_Cell3ComplexK32_chi` — inline ↔ structured form
    `closed_3mfd_targets_match_Cell3Complex` — realization predicate consistency

**Still missing**:
  · Topological 3-mfd structure verification (not just Euler-target
    match) — requires attaching-map formalization (significant infra).
  · JSJ-torus-cut lift from graph cut to manifold cut.

**Falsifier potential**: LOW unchanged (structural pillar deepening).

---

### FW-3 — K_{NS,NT}^{(c)} higher-chartBase generalization  [UNIVERSAL CLOSURE — PARTIAL]

**Current state**: `Generalization.lean` (~14 PURE) — chartBase
∈ {4..8} extended + **universal Prop-level characterization**.

Universal closure added 2026-05-22:
  · `sym3_c2_force_K32` — Sym(3) ∧ c=2-binary-cover forces
    `{n,m}={2,3} ∧ c=2`, without chartBase bound.
  · `sym3_c2_iff_K32_or_K23` — biconditional iff form.
  · `filter_passes_only_chartBase_5` — filter passers live only
    at chartBase = 5 (asymptotic across all Nat).

The two representation-structure filters alone determine the
deployment; b₁=8 conjunct is automatic.  No per-chartBase ≥ 9
enumeration needed.

**Still missing** (Boolean-level corollary):
  · Boolean ↔ form `passesCohomologyDepthFilter n m c = true ↔ ...`
    — blocked by `Bool.and_eq_true` rewriting through propext.
    Workaround: use the Prop-level `sym3_c2_iff_K32_or_K23` for
    downstream proofs; Boolean form is sugar.

**Effort spent**: ~1 session (universal closure achieved cheaply
via structural deduction; per-chartBase enumeration obviated).

**Falsifier potential**: MEDIUM unchanged.  The universal theorem
makes the falsifier sharper: ANY (n, m, c) passing both Sym(3) +
c2-binary-cover MUST be (3,2,2) or (2,3,2).

---

### FW-4 — E³/H³/H²×ℝ direct realization (metric geometries)  [PARTIAL DEEPENED]

**Current state**: `MetricGeometries.lean` (~15 PURE) — Möbius P
mod-k Lens family extended to F_2 / F_3 / F_5 / F_7 / F_11 / F_13
+ **F_5 uniqueness structural result**.

Deepening added 2026-05-22:
  · `F5_unique_nil_collapse_small_primes`: across primes 2..23,
    only `p = 5` collapses the Möbius P discriminant (= 5).  This
    establishes F_5 as the *structurally unique* Nil-Lens.
  · `F13_lens_irreducible`: extends prime table to F_13.
  · `mod_k_lens_family_F5_unique_close`: 213's `d = 5` fractal
    base aligns with the unique Nil-producing Lens — not arbitrary.

**213-native metric type added 2026-05-22** (`Geometry/MetricTypes.lean`,
16 PURE):
  · `MetricSignature` inductive type with 8 constructors (E³, S³,
    H³, S²×ℝ, H²×ℝ, ~SL₂, Sol, Nil)
  · `LensChoice` inductive type with constructors for identity,
    ∂Δⁿ-boundary, real-trace, real-trace-plus-axis, integer-lattice,
    Pell-spiral, mod-p (parameterized)
  · `classify : LensChoice → MetricSignature` total function
  · 8 individual `classify_*` witnesses (one per Thurston geometry)
  · `isIsotropic` / `isAnisotropic` predicates with 3 + 5 = 8 partition
  · `F5_unique_Nil_classifier` (signature-level F_5 uniqueness)
  · `metric_signature_classifier_capstone` (16-conjunct)
  · Bridge in `MetricGeometries.lean`:
    `mod5_Lens_matches_Nil_signature` — algebraic ↔ signature
    `F5_Nil_bridge` — 6-conjunct bundling both sides

**Still missing** (full real-metric-tensor formalization):
  · Real-valued metric tensors (E³ = Euclidean, H³ = hyperbolic,
    etc.) — by design absent from 213; the signature classification
    is the 213-native replacement.
  · Promotion to "modulus k forces geometry G_k" uniqueness
    theorems for k ∈ {2, 3, 7, 11} beyond F_5 ↔ Nil — needs deeper
    Lens-classifier theory.

**Falsifier potential**: MEDIUM unchanged.  F_5 uniqueness now at
two formalization levels (algebraic discriminant + signature
classifier) — falsifier sharpened.

---

## §2.  R1 knots — residual

From G121 §6, the knots survive R1 close in reduced form:

| Knot | R1 status | Residual open part |
|---|---|---|
| **M1** | TWO-ROUTE CLOSE (atomicity + Möbius, K_{3,2}^{(c=2)}) | Generalize M1-close to all chartBase ≥ 9 → folded into FW-3 |
| **M2** | ABSTRACT CLOSE 2026-05-22 via `KChartLens NS NT c` structure (`KChartLensAbstract.lean`) | `KChartLens` type + canonical instances K_{3,2}/K_{3,1}/K_{1,4} + V32Betti compatibility for K_{3,2} via `m2_abstract_close`.  Full V32Betti-style derivation for arbitrary K_{NS,NT}^{(c)} still open (requires per-deployment cohomology files) |
| **M3** | downstream (physics interpretation) | NT-axis split into time + self-pointing.  **Re-activate only when physics push reactivates**; not a Lean-formalizable item in current state.  See G121 §6.3. |
| **M4** | doc-level (stereotype-matching warnings) | Maintain "this is not Kaluza-Klein" anchor in any expansion; cite G121 §6.4.  Permanent doc-hygiene, no marathon. |

M1 and M2 are fully subsumed by FW-3 (chartBase generalization).
M3 is dormant.  M4 is a permanent style constraint, not a task.

---

## §3.  Narrative-deepening items (I-series from G121 R1+)

Below-FW-priority refinements surfaced in G121 R1+ tail
("next-session entry point" §3).  None are blocking; all could
be picked up opportunistically:

| ID | Topic | Effort | Status |
|---|---|---|---|
| **I-1** | 8-geometry ↔ Sym(3) basis-correspondence (explicit basis for 2·trivial ⊕ 3·standard ↔ 3 iso + 5 aniso assignment) | small (1-2 sessions) | **CLOSED** ✅ `sym3_basis_thurston_mapping` in `CrossFrame.lean` (2026-05-22) |
| **I-2** | Filled.lean → 3-cell complex extension | subsumed by FW-2 | — (subsumed) |
| **I-3** | Ricci flow ↔ chart-Lens averaging (full ε-Lens treatment) | small-medium (2 sessions) | **CLOSED** ✅ `IsRicciModulus` structure + `K32_isRicciModulus` instance + `ricci_eps_lens_full_integration` (Ricci.lean, 2026-05-22) |
| **I-4** | Poincaré ↔ trivial-loop-residue (refine via `V32Betti.b0_eq_1` connectedness work) | small (1 session) | **CLOSED** ✅ `poincare_two_layer_trivial_loop` in `Poincare.lean` (2026-05-22) |

I-2 is duplicate of FW-2.  I-1 / I-3 / I-4 are independent micro-marathons.

---

## §4.  Cross-frame deepening (G121 R1+ §C5)

The structural mapping `Geometrization 8 + gluon octet +
K_{3,2}^{(c=2)} cohomology + Möbius P pentagonal closure → one
algebraic spine` (theory chapter §"Cross-frame connections")
already cites four chapters.  Open: a single capstone theorem
bundling these four sources into a unified statement.

| ID | Statement (informal) | Effort | Status |
|---|---|---|---|
| **X-1** | Capstone theorem: "Sym(3) decomposition of 8-element substrate is invariant across {Geometrization classification, gluon octet, HC_K32 cohomology, Möbius P mod-5 closure}" | small (1 session, mostly bundling existing PURE results) | **CLOSED** ✅ `G121_X1_sym3_cross_frame_capstone` in `lean/E213/Lib/Math/GeometrizationConjecture/CrossFrame.lean` (2026-05-22) |

X-1 is a meta-capstone — adds no new mathematics, just records the
4-way convergence as a single citable theorem.

---

## §4.5  Spin-off marathons (post-G128 numbering)

The G128 sweep leaves three items that don't fit a single follow-up
marathon scope; each gets its own G-number for future launch:

| G-number | Topic | Status | Note |
|---|---|---|---|
| **G129** | M2 universal V32Betti-style generalization | open marathon, ~95 PURE est. | `G129_v32betti_parametric_generalization.md` |
| **G130** | BracketCauchy ↔ IsRicciModulus typeclass-bridge | open marathon, Option A ~40 PURE est. | `G130_bracket_cauchy_ricci_functor.md` |
| **(no G)** | FW-1 signed Donaldson count | **SUPERSEDED by G126** — meta-research at the 213/standard-math boundary; redirect to cork-frame | See §1 FW-1 entry; cork-frame supersedes via `G126_akbulut_cork_213_native.md` |
| **G126** | Akbulut cork as 213-native exotic-structure framework | open marathon, ~120 PURE est., 8-12 sessions | `G126_akbulut_cork_213_native.md` — **HIGH-PRIORITY** alternative to FW-1; converts the unresolved sign problem into a concrete 213-internal cork-twist enumeration with all ingredients pre-existing (M_S01 involution, K_{1,4} tree as cork, ∂Δ⁴ = S³, tree-critical coexistence) |

FW-1 stays unassigned: its open piece is "what's the 213-native
sign-rule for Sym(3)-orbits, AND/OR how to compare to Donaldson
invariants" — these are theoretical questions to settle BEFORE a
Lean marathon launch is well-posed.

---

## §5.  What this registry is NOT

  · **Not a marathon launch**.  FW-1 and FW-4 are marathon-shaped
    but launching either requires explicit user direction (matches
    `marathon-start` skill convention).
  · **Not a re-opening of R1**.  R1 is closed and promoted; this
    registry catalogs *follow-ups*, not corrections.
  · **Not a precision-theorem candidate**.  Per G121 §8 + theory
    chapter "Below DRLT Validation Standard" — none of FW-1..FW-4
    is a precision theorem yet.  FW-1 has the strongest path
    toward falsifier-form (Donaldson-comparable count).
  · **Not a renumbering proposal**.  The G121-internal G122-G130
    labels are kept as historical references in §0; new marathon
    numbers are picked at launch time only.

---

## §6.  Recommended ordering (when work resumes)

Conditional on user direction; default sequencing:

1. ~~**X-1** (1 session, easy capstone)~~ — **DONE** 2026-05-22.
2. ~~**I-1** + **I-4** (2-3 sessions combined)~~ — **DONE** 2026-05-22.
3. ~~**FW-3** (medium marathon, universal closure)~~ — **DONE** 2026-05-22
   (Prop-level closure; Boolean ↔ corollary deferred).
4. ~~**FW-2** (partial deepening)~~ — **DONE** 2026-05-22
   (3-mfd target catalog + JSJ-cut canonical; full 3-cell complex deferred).
5. ~~**FW-4** (partial deepening)~~ — **DONE** 2026-05-22
   (F_5 uniqueness for Nil collapse; metric formalization deferred).
6. ~~**FW-1** (marathon, anchor)~~ — **ANCHORED** 2026-05-22
   (`sym3GaugeInvariant` + `exotic_4mfd_scaffold`; substantive
   enumeration is the continuing marathon for future sessions).

I-3 is parallel to anything; can interleave.

---

## §7.  Cross-references

### Closed sources
  · `research-notes/G121_dim4_self_pointing_axis.md` — full G121 narrative
  · `theory/math/geometrization_conjecture.md` — promoted R1 chapter
  · `lean/E213/Lib/Math/GeometrizationConjecture/` — Lean sub-tree (12 files + INDEX)

### Registry kin
  · `research-notes/G107_action_items_registry.md` — G90-G106 items, same shape
  · `HANDOFF.md` open work §B — G107 still-open subset

### Anchor docs
  · `theory/PROMOTION_CRITERIA.md` — when does an FW item promote?
  · `seed/AXIOM/08_falsifiability.md` §8 — Validation Standard
  · `seed/META_SCAN_ARCHETYPES.md` — abstraction patterns for FW-3
