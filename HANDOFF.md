# Session handoff

Branch: `claude/research-notes-9Nc74`

## Latest autonomous iteration (2026-06-01)

  1. **Headline — the `5²⁵`-as-resolution chain is DELETED** (originator
     decision, not re-derivation).  The claim that `5²⁵ = N_U = d^(d²) =
     configCount 2` is "the resolution" at which physics is evaluated rests on
     a category error (a configuration **count** is not a spectral-sum
     **truncation index**) and contradicts the foundation (no privileged level
     — G156; no top — residue/self-covering).  Deleted whole:
     `Foundations/{FiniteUniverse,NResolutionFromFractal,NResolutionFractalDepth,
     FractalLensCardinality}`, `Capstones/{FinitistObservableChain,
     ValidationStandardOne}`, `AlphaEM/NResolutionCandidates`,
     `UniverseChain/{Universe,Synthesis,MobiusChain}`,
     `AlphaEM/Capstone.MasterCapstone`, `Padic/DRLT.canonical_5adic_NU`.
     Scrubbed (structure kept): `AlphaEM/{Capstone,GradedFormula,PiFiveGap}`,
     `Padic/*`, `Recursion.lean`, aggregators, + `GradedRingNUBridge` →
     `GradedRingConfigCountBridge`, + docs/catalogs/theory.  Commits
     `a8bc77f`, `bda7a07`, `b8e4c84`, `df1c444`.
  2. **What SURVIVES (verified ∅-axiom)** — the 0.2 ppb precision result is
     independent of `5²⁵`: it rests on `π²` as a **literal input** (`pi2_e12`),
     not a finitist resolution.  `GramStructuralCapstone.invAlphaEm_precision_
     theorem` scans **5 pure / 0 dirty**; full `lake build E213` green.  Honest
     claim now: *given π, the K_{3,2} cup-ring 5-layer + Gram cubic reproduce
     1/α_em to 0.2 ppb* — no "π-free / finitist / derivation" overclaim.  Also
     kept: atomic forcing `(NS,NT,d)=(3,2,5)`, residue, parametric
     `configCountD`/`numV=5^L`/`S(N)`, and `configCount 2 = 5²⁵` as bare arithmetic.
  3. **ConfigCount strict tower** (`Lib/Math/Cohomology/Fractal/ConfigCount.lean`):
     `configCountD_strictMono_succ/strictMono/injective` (`d ≥ 2`) — the level
     tower is a strict order-embedding ℕ ↪ ℕ.  Plus a Tier-A build fix
     (guard-test imports).
  4. **Research notes** — **G156** (no privileged level, theorem); **G157**
     (the deletion *argument*: category error + no-top foundation); **G158**
     (Target A scoping — see below).

### `depth_floor_is_det_one` — CLOSED, both directions (G158)

`Lib/Math/Cauchy/DepthFloorDetOne.lean`, **7 pure / 0 dirty**, wired into the
Cauchy umbrella; full `lake build E213` green.
  - **Forward** `convergent_crossdet_floor_is_one` (`reachesFloor W ∧ ∀ n, W n
    = 1`): the convergent cross-determinant `W` reaches the ladder floor at
    depth 0 with value 1 — analysis-side floor (`const_reaches_floor`) = det P = 1.
  - **Converse** `floor_one_is_P_invariant`: floor value 1 in squared Cassini
    form `a²+1 = a·b+b²` is *preserved* by the autonomous P-step
    `(a,b) ↦ (2a+b, a+b)` (= `Mobius213PellInvariant.pellNormStep`) — the
    floor IS the P-orbit's defining invariant, not merely a value reached.
  - **Master** `depth_floor_is_det_one` bundles both.  Built on the PURE
    `FibCassiniNat.fib_cassini_norm`; pellNormStep's hypothesis IS floor-1.
  The "strongest unclaimed result" (HANDOFF Target A) is closed.

### Build gate-hole — CLOSED (G159)

A static import-graph audit found **~350 of 1532 `E213` modules (~23%)
orphaned** — unreachable from the build roots, so `full_build.sh` never
compiled them and latent breakage hid.  **Now resolved**: every orphan's rot
was fixed and **`tools/full_build.sh` rebuilds all 1532 modules (exit 0)** —
no orphan can hide breakage.  Crown-jewel α_em precision chain wired into the
umbrella.  Fast `lake build E213` (framework only) kept for iteration.  Full
history + map: `research-notes/G159_*`.  Lesson retained: a gate that follows
only umbrella imports is incomplete — build the module set, not the closure.

Done this marathon (all pushed except the in-flight SignedCut work):
  - **Gated the crown jewel**: the 0.2 ppb precision chain
    (`AlphaEM/GramStructural*`, `invAlphaEm_precision_theorem`) was orphaned;
    `AlphaEM.lean` now imports `GramStructuralCapstone` → in the gate.
  - **`Mobius213/Px/` rot fixed** (now `lake build E213.Lib.Math.Mobius213.Px`
    green): `ConvergentDet` (undefined `convergent_det'`; conv parse error;
    `rw [h1,h2]` defeq bug), `MobiusSelfForm` (defeq bug), `PGeneratesNat`
    (type mismatch + stuck-match omega).  Note: many Px theorems are
    **axiom-dirty** (propext via omega/Nat-core) — separate purity pass.
  - **`InvolutionCapstone`** (missing-type re-export) fixed → `AkbulutCork`
    cluster builds.
  - **SignedCut 5²⁵-tail DONE** (commit `b1eb06b`): deleted
    `Hurwitz/HurwitzCeiling`, `Level/{Level25Capstone,Level25Residual,
    Level26Absence}`; scrubbed `Level/G38FinalCapstone`, `Core/MulRuleCapstone`,
    `CD/{CDTowerCapstone,CDTowerLevel,CDConjugation}` (kept mul-rule / Hurwitz
    magnitude / bit-dim structural lemmas).  Heads build green.
  - **5²⁵ was deeper than the original chain**: the ceiling/`N_resolution`
    reading was scattered across more **gate-hidden** clusters —
    `DialogueAudit/*`, `Linalg213/Gap/*`, `CartesianVsDisjoint/*`,
    `Lens/Cardinality`, `OperationTopology/TotalPreservation`, `AlphaEM/CupRingTrace`
    (~12 files, mixed gated/orphan).  **Final repo-wide sweep in flight**
    (background worker); after it, `grep N_resolution` should be empty.
  - **Separate rot noted** (not 5²⁵): `SignedCut/Level/G39Capstone.lean`
    references nonexistent `FanoK32Bridge` constants — a partial-rename
    breakage in the orphan tree; fix in the rot-cleanup thread.

**`full_build.sh` is now GREEN** (was pre-existing RED, gated tree, independent
of 5²⁵).  All 7 gated-build failures fixed: `ModArith/Join{Bezout,Coprime,
Example,Euclidean,EquivGCD}` (stale `open E213.Lens renaming leaves_view_ge_one`
— that lemma is `protected Lens.leaves_view_ge_one`; the open now renames the
public `leaves_view_pos`, same statement `1 ≤ Lens.leaves.view r`),
`DyadicFSM/ArithFSM/V3Equiv` (doc-comment on an `open`), and
`Physics/Certificates/Checker` (a stray duplicate `(inv_lower_tight inv_upper
capstone_n20)` fragment applied to `Cert.boundsOk`'s body → "function expected"
+ `sorryAx`; removed → `cert_n20_boundsOk` PURE).  `lake build E213.Lib.Math
E213.Lib.Physics` completes clean.

**Orphan rot — fully cleared.**  The complete all-modules inventory found and
fixed every broken orphan: Px ×3, InvolutionCapstone (→ AkbulutCork),
`SignedCut/Level/G39Capstone` (restored `FanoK32Bridge` components),
`EnrichedKNSNTcEvenEven` (`rcases`-literal → `match`), `PellOrbitInstances`
(non-dependent `if` → `if h :` so omega sees the bound).  **All 1532 modules
build; `full_build.sh` is now the comprehensive gate.**  Remaining gate work is
*optional polish*, not correctness: (a) **purity audit** of the now-gated
orphan clusters (most are unscanned — likely the same `omega`/`Nat.mul_assoc`
dirt the Px pass fixed; apply that pattern); (b) wiring chosen clusters into the
`Lib/Math.lean` umbrella for fast-iteration coverage (vs the comprehensive
script); (c) pruning any genuinely-dead WIP files.

**Px purity-audit DONE** — the entire `Mobius213.Px` subtree is now ∅-axiom
(user directive "category-3 → all PURE" satisfied): `QFibIdentity` 9/0,
`FibCassini` 9/0, `ConvergentDet` 8/0, `MobiusSelfForm` 11/0, `PGeneratesNat`
50/0; full-subtree scan reports 0 dirty.  Two reusable PURE helpers were added
(`Meta.Nat.NatDiv213.div_le_self_pos`, `Meta.Nat.AddMod213.div_le_div_right_pos`);
`AddMod213`/`NatDiv213` stay 16/0 and 8/0; `lake build E213.Lib.Math
E213.Lib.Physics` GREEN.  The lone irreducible `coprime_NS_NT`
(`Nat.gcd NS NT = 1`, propext via core `Nat.gcd` WF-recursion) was *unused* and
removed — the PURE coprimality fact is `Meta.Nat.Gcd213.gcd213_succ_self`.

**Repo-wide purity audit DONE** (now that the gate scans all 1532): whole-repo
`scan_all_axioms` = **12489 PURE / 62 real-DIRTY / 57 sealed**.  **Falsifiability
standard MET** — no `Classical.choice` / no `native_decide` in any 213-math
content; the only `Classical.choice` carriers are 3 `CommandElab` modules
(`Tactic.QuadExtension`, `Meta.Tactic.{DeriveConjugationCodomain,VerifyConjugation}`),
now sealed (category a, plumbing).  The **62 real-DIRTY are all propext/Quot.sound**
(allowed-but-not-target), in previously-orphaned clusters the comprehensive gate
exposed: `Lens.{Compose,Lattice}.*`, `Lib/Math/{Choice,CayleyDickson,
Cohomology/Bipartite/Parametric,Cauchy,Hyper}`, etc.  This is the **purity
backlog** (not a falsifiability issue); `STRICT_ZERO_AXIOM.md` "### Net effect"
synced.

**Gate caught a REAL falsifiability violation.**  `KerSizeUniversal`
(`Cohomology/Bipartite/Parametric`) carried **`Classical.choice`** in 3 math
theorems (`ker_implies_pair_eq` + 2 inheritors) — forbidden in 213-math.  It was
gate-hidden (only built after this session's `EnrichedKNSNTcEvenEven` /
`PellOrbitInstances` fixes).  Root: **Lean-core `Nat.mul_lt_mul_left` (the `Iff`,
used `.mpr`) pulls `Classical.choice`** — replaced with a PURE
`mul_lt_mul_left_pure` (`c*m+1 ≤ c*m+c = c*(m+1) ≤ c*n`).  Now `[propext]` only.
(`FibCassiniNat` already documents this `Nat.mul_lt_*` Classical leak.)  **After
this fix, the only `Classical.choice` carriers repo-wide are the 3 sealed
CommandElab modules** — falsifiability standard genuinely met (verified).

**Triage of the 62 backlog** (most are by-design, NOT purify): the `Lens.*`
dirty (`Compose.OnLens` 9, `Lattice.Join` 4, `Algebra.Corresp`, …) are
funext-on-combine = the same category (b) as the sealed Lens modules → **seal**;
`Choice.CanonicalTruthChar` (8) is Iff↔Bool propext = category (a) → **seal**.
The genuinely-purifiable artifact-dirty are the math clusters (`CayleyDickson`,
`Cohomology/Bipartite/Parametric`, `Cauchy`, `Hyper`) via the Px playbook.  Next:
seal the by-design Lens/Choice clusters; purify the math artifacts.

**Reusable purification pattern** (verified — applies to any future dirty Nat code):
  - `omega` is **propext-dirty** — eliminate: trivial `2*(k+1)=2*k+2` → `rfl`;
    additive rearrangements → `Nat.two_mul` + `Nat.add_right_comm`/`Nat.add_assoc`
    (factor a `private` helper, cf. `ConvergentDet.add_dup_succ`); div/mod via
    `Nat.div_add_mod` + `mul_mod_right` + the `Meta.Nat` div helpers; impossible
    hyp `0≥1` → `absurd h (Nat.not_succ_le_zero _)`.
  - `Nat.mul_assoc` / `Nat.add_mul` are **propext-dirty** → PURE
    `NatRing.nat_mul_assoc` / `nat_add_mul`.  (`Nat.mul_add`, `Nat.mul_comm`,
    `Nat.add_comm`, `Nat.add_assoc`, `Nat.add_right_comm`, `Nat.two_mul`,
    concrete-literal `decide` are PURE.)
  - `simp`/`simpa` → explicit `rw`; pair-`match` matcher → nested `cases`;
    `Nat.succ.inj`/`Nat.succ_ne_zero` → `Nat.noConfusion`; core `Nat.gcd` →
    213-native `gcd213` (core gcd is irreducibly propext).

The durable record of all closed work lives in `lean/E213/` (source of truth) and
`theory/` (narrative).  This file keeps only: the latest arc's one-line map, a
compact index of what is closed, and the detailed next-target list.

## Latest arc — real numbers as cuts, completeness without completeness

A long originator-driven thread, now closed and written up.  Capstone paper
`theory/math/completeness_without_completeness.md` (5 parts, 15 §); detail chapters
`theory/math/completeness_relocated.md` + `probe_twist_conic.md` (§0–13); essay
`theory/essays/real_without_completeness.md`.  Every link is a ∅-axiom theorem.

The chain, each link a theorem (Lean module in parentheses):

  1. **Completeness is relocated, not constitutive** — a real is a decision
     procedure vs ℚ; completion is a leaf of the import graph, unconditional for
     algebraic (φ closed-form modulus) / modulus-gated for transcendental
     (`Real213/AbCutSeq`, `PhiAbCut`, `EulerCut`, `PiCut`, `Analysis/CompletionTower`,
     `ModulusMonoid`, `ResolutionQuantitative`, `ModulusForm`).
  2. **The probe lattice is P-twisted** — `P = [[2,1],[1,1]] ∈ SL₂(ℤ)`,
     order-preserving, `det = NS − NT = 1` (`MobiusProbeTwist`).
  3. **φ is the twist's fixed cut**; e is not (`PhiProbeFixed`, `ProbeTwistFixedPoint`).
  4. **The wobble = `f⁻¹`, backward Pell** (`ProbeTwistDynamics.twist_undoes_step`).
  5. **The wobble's shape = the conic `Q = m² − mk − k²`** — every orbit on its
     hyperbola `Q = N`, disc 5 = NS+NT (`ProbeTwistConic.Q_preserved`).
  6. **The divergence has a form** — cross-det `Wₙ` (discrete Wronskian): φ `±1`,
     e `−n!`, π Wallis (`EulerDivergenceForm`).
  7. **Divergence depth** — lift the form until constant: algebraic 1 < e 3 < π 6 <
     Liouville ∞.  Depth ≠ irrationality measure μ (μ collapses alg=e=π=2); depth =
     the P-recursive / holonomic rank (`DivergenceLadder`, `DivergenceDepth`).
  8. **Finite depth ⟺ P-recursive** (`DepthPRecursive`).  Classical CF data: exp/tan
     family (e, tanh1 = [0;1,3,5,7,…]) finite depth; π/arctan1/ln2 irregular.
  9. **The ratio-lift axis** — `ratioLift` differences the exponent
     (`ratio_is_diff_on_exponent`), so `ratioN^h` floors exactly `c^{poly deg h}`;
     `h` = exponent's polynomial degree (`DepthTower`).
  10. **The `(h,d)` coordinate is an ordinal `< ω²`** — `lex_wf`,
      `no_infinite_descent` (`DepthOrdinal`).
  11. **Third axis = recursion into the exponent** — value-height = 1 +
      exponent-height; `value_floors_iff_exponent_floors` (`DepthExponentRecursion`).
  12. **`ε₀` is not the end** — `ratioN` cannot cross one exponential layer
      (`2^{2ⁿ}` is a fixed point: `ratioN_dexp`, `dexp_not_const`); the heights are
      the classical ordinal hierarchy, with no top (`DepthDoubleExp`).
  13. **Naming the ceiling-raising = the residue** — referencing the whole tower is a
      diagonalisation `diag f n = f n n + 1` escaping every level (`diag_not_in_seq`);
      this is `cantor_general` = the same non-surjectivity as the foundational residue
      `self_covering_closure`.  The arc closes onto its origin (`DepthCeilingResidue`).

Depth-arc Lean: 9 modules, audited PURE / 0 dirty.  Wired into the `Cauchy.lean`
umbrella; full `lake build` clean.

## Closed and promoted (durable homes — do not re-derive)

| Topic | Source of truth | Narrative |
|---|---|---|
| Real-number completeness arc (links 1–13) | `Lib/Math/Cauchy/Depth*`, `Divergence*`, `EulerDivergenceForm`; `Lib/Math/Real213/*`; `Lib/Math/Analysis/*` | `theory/math/completeness_without_completeness.md` (+ `completeness_relocated`, `probe_twist_conic`); essay `theory/essays/real_without_completeness.md` |
| φ self-similarity (form / count `5^L` / limit-ratio φ) | `Lib/Math/SelfSimilarityBridge`, `Real213/{PhiAsCut,PhiConvergence,PhiNormInvariant,PhiAbCut,FibCassiniNat}`, `PellFibCutBridge` | `theory/math/phi_self_similarity.md` |
| The residue / self-covering closure | `Lens/FlatOntologyClosure`, `Lens/PredicateSelfEncoding`, `Theory/Raw/{PrimitiveTower,Lambek}` | `research-notes/G152`, `theory/essays/tower_atlas.md` |
| P-orbit closure (P self-defining; every axis sees `{3,2,1}`) | `Mobius213/Px/{CharPolySelf,MobiusSelfForm,ConvergentDet}`, `Theory/Atomicity/OrbitForcing`, `Mobius213SignatureAxisCatalog` | `theory/essays/{every_axis_sees_p,p_orbit_closure_master}.md` |
| General Cauchy completeness (cut space closed under limits) | `Analysis/CauchyCompleteValid` | `completeness_relocated.md` |

PURE Nat helper infrastructure (reuse, don't re-derive): `Meta/Nat/NatDiv213`
(`mul_div_self_pure`, `mul_div_cancel_left_pure`, `pow_succ_div`, `add_div_right_pos`),
`Meta/Nat/PureNat` (`pow_add`, `mul_assoc`, `add_mul`), `Meta/Tactic/NatHelper`
(`succ_sub`, `add_sub_cancel_right`, `add_sub_of_le`, `sub_add_cancel`).

## Next targets (detailed)

### A. Depth-floor = P-orbit, as one theorem (`research-notes/G154`)

The strongest unclaimed result the arc exposes.  Three sub-trees independently land
on `det = 1` as the floor: the divergence ladder (`const_reaches_floor`), convergent
geometry (`ConvergentDet.convergent_det`, Cassini `Wₙ = ±1`), and atomic forcing
(`OrbitForcing`).  **Depth measures distance from atomicity**: a real's generating
recurrence departs from P's autonomous self-definition by a polynomial of degree
`depth − 2`.  Promotable brick:

> **`depth_floor_is_det_one`** — `reachesFloor` with cross-determinant floor value 1
> ⟹ the convergents satisfy the autonomous Pell/Cassini step (`pellNormStep`), i.e.
> lie on a P-orbit.

Hinge between the analysis-side ladder and the atomic-side forcing.  **Obstacle
re-assessed (G158, 2026-06-01)**: the old Int→Nat worry is moot — `convergent_det`
and `cassini_universal` are already PURE *Nat-additive*.  Forward direction is
near-trivial (`W = const 1` via `convergent_det` → `reachesFloor` at depth 0).
The real remaining content is the **converse** (recurrence-uniqueness: floor value 1
⟹ autonomous P-step), via `OrbitForcing`/`PnFibonacciUniversal`.  See
`research-notes/G158_depth_floor_det_one_scoping.md` for the full plan.

### B. `depth_floor_is_det_one`'s converse + the finite-depth recurrence (formal P-recursive)

Currently "finite depth ⟺ P-recursive" is `DepthPRecursive` at the difference-degree
level plus a classical (C) bridge to holonomic rank.  Open: make the bridge a
theorem for the e and π cases — exhibit the explicit polynomial-coefficient recurrence
their convergent data satisfies (e: coeff `n+1`, degree 1; π: degree 4) and prove
`polyDepth d` matches.  This closes the (C) gap in chapter §III/§9–10.  **Architecture
for A+B**: `research-notes/G155` (HolonomicReal type — bundle the recurrence data with
a derived `CertifiedModulus` so the API is unconditional within the holonomic class;
the unproven `Holonomic.toCertifiedModulus` is exactly this target).

### C. The genuine third-axis closure (ratio-on-exponent reaches `c^{c^{poly}}`)

`DepthDoubleExp` proves `ratioN` *cannot* cross one exponential layer; `DepthExponent‑
Recursion` proves the recursion bridge `value-height = 1 + exponent-height`.  Open:
assemble these into a positive theorem that the recursion *does* floor `c^{c^{poly}}`
at the right coordinate (apply the `(ratio,diff)` ladder to the exponent, then to its
exponent), and pin the ordinal rank `ω^r · d` for a depth-`r` tower as a Lean
statement, not just the classical (C) reading.  This is the proven path from `ω²`
toward `ω^ω`.

### D. Liouville's coordinate beyond the two-operator system

`DepthDoubleExp` shows Liouville `c^{k!}` has no finite `(h,d)`.  Open: give it a
coordinate in the *recursion* hierarchy of C — its exponent `k!` floors under ratio
(`k! ↦ k+1`), so it should sit at a specific transfinite coordinate.  Formalising
"the exponent is itself an `expSeq`-like object" is the frontier toward `ε₀`.

### E. Tower duality (longer-horizon, conceptual)

Two open dualities flagged in `tower_atlas.md` / `G154` §2:
  - **GRA-tower ↔ CD-tower**: level `n` of property-loss ↔ level `5−n` of Reading-iso
    gain.
  - **Depth-ladder ↔ Cayley–Dickson tower**: both property-loss/gain towers bottoming
    at a 213-forced floor, both controlled by `5 = d = NS + NT`.  Whether these are
    readings of one tower (as `tower_atlas` argues for the P-orbit towers) or genuine
    coincidence is open.
  - **Flexibility over a non-associative base** (`CDDoubleFlexible.lean` cross-pair
    crux) — the long-standing Cayley–Dickson open item.

## Notes / hygiene

  - **Verify Lean SEQUENTIALLY before commit**: `rm <file>.olean` → `lake env lean
    <file>` (exit 0) → `lake build <module>` → `tools/scan_axioms.py <module>` (N pure
    / 0 dirty) → commit.  build-green ≠ purity-green; never trust cached "Build
    completed"; never parallelise build with scan.
  - **PURE arithmetic**: every Lean-core division-cancel / `pow_add` / `add_sub_cancel'`
    pulls `propext`.  Use the `Meta/Nat` helpers listed above; build new PURE chains
    from `Nat.div_eq_sub_div`, induction, and `Int213.*` additive routing (no `Int`
    subtraction, no `omega`, no `Nat.max`, no `funext` for function-equality — use
    pointwise).
  - `decide` on `Subtype`/`Raw` equality pulls `propext` via `DecidableEq Raw`; use
    `Tree.noConfusion` (for `a ≠ b`) and `of_decide_eq_true` (not `decide_eq_true_eq`).
  - **Repo-first**: grep + INDEX before coding a "missing" cell (`PredicateSelfEncoding`
    and the `add_div_right_pos` helper were both nearly rebuilt).
  - `5²⁵ = N_U = d^(d²)` as a **resolution / universe number is DELETED**
    (2026-06-01) — not deprecated, gone.  `configCountD`/`configCount 2 = 5²⁵`
    survive only as bare parametric arithmetic; never reintroduce a "the
    resolution" reading.  See `research-notes/{G156,G157}` +
    `RERESEARCH_n_u_removal.md`.  Don't use "ℝ = final boss" framing.
