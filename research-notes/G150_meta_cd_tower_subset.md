# G150 — 메타-CD-타워: 4-Type Base × CD doubling = CD가 부분집합

**Date**: 2026-05-29 (trimmed 2026-05-29: closed phases promoted;
2026-06-01: flexibility crux closed, Phase 7 vertical-reindex opened)
**Status**: Moufang norm-composition + flexibility sub-trees **CLOSED**.
The polarization framework (`Meta/Algebra213/CDDoubleMoufang.lean`,
`CDDoubleAlternative.lean`, `Levels/SedenionZeroDivisor.lean`) and the
closed-phase journal now live in the permanent tier:

  - **Theory**: `theory/math/cayley_dickson/algebra_tower.md`
    (§"Norm composition at the octonion-analog layer") +
    essay `theory/essays/cd_tower_polarization.md`.
  - **Atlas**: `theory/essays/tower_atlas.md` (CD tower as one Lens
    reading of the P-orbit; boundary vs other repo "towers").
  - **Session journal**: `HANDOFF.md` (Phase 1–4 commit history,
    flexibility cross-pair scoping).

This note now holds only the **still-open scratch** (Phase 5–6) plus
the originating observation.

## 핵심 관찰 (originating insight)

> "타워를 올라가는게 Raw의 2페어나 3페어를 하는거자나 (1, w, w^2,
>  이것도 있음). 이렇게 타고 올라가다 보면 cd 곱셈의 레이어들과
>  만나는 지점도 있을거니깐, cd 타워가 이 타워의 부분집합인거 같아서"
> — Mingu Jeong 2026-05-29

고전 Cayley-Dickson tower = **Type A 단일 column**.
메타 타워 = (Type 선택 × CD doubling layer) 매트릭스.
SHIFT RULE = 매트릭스 cell 간 isomorphism.

## 4 Type × CD doubling matrix

| Type | Base | atom 구조 | 사용자 매핑 |
|---|---|---|---|
| **A** | ZI = ℤ[i] | (1, i) 2-pair | "2페어" |
| **B** | ZSqrt[D≥2] = ℤ[√D] | (1, √D) 2-pair w/ D-twist | "2페어 변형" |
| **C** | ZOmega = ℤ[ω], ω²+ω+1=0 | **(1, ω, ω²)** 3-element | **"(1,w,w²)" — 정확 일치** |
| **D** | Hurwitz | modified quaternion | quaternion 변형 |

```
Type A:  ZI → Lipschitz → Cayley → Sedenion → Trigintaduonion → Pathion
           2      4         8        16          32              64
Type B:  ZSqrt → L3T → L4T → L5T → L6T → L7T → L8T → L9T
                 2     4     8     16    32    64    128   256
Type C:  ZOmega → ZOmegaDouble → ZOmegaQuad → ZOmegaOct
           2          4              8           16
Type D:  Hurwitz → HurwitzL2 → HurwitzL3   (24 → 48 → 96 units)
```

Type E는 reject (`Misc/TypeE_Rejection.lean`) — 4-row가 complete 진술.
dimension은 layer마다 ×2 (CD doubling).

## SHIFT RULE — 타워 간 만남점 (concrete cases closed)

`ZSqrtMinus2Findings.shift_iso_L3`: ZI units (Type A L2, 4 원소) ≅
L3T units (Type B L3, 4 원소) at unit-loop level — 다른 Type, layer가
1 다른데 구조 동일.  `SedenionOrder4Monopoly`: Type A L5 ≅ Type B L6
(order distribution `{1, 1, 30}` 일치).
→ 사용자 직관 "cd 곱셈의 레이어들과 만나는 지점" = SHIFT RULE 좌표.

## 무엇이 누락? — Parametric meta-framework

| 있는 것 | 없는 것 |
|---|---|
| 4 Type 각각 구체 형식화 | 하나의 parametric framework |
| SHIFT RULE 구체 case (`shift_iso_L3`) | SHIFT RULE 추상 functor 진술 |
| `TowerFixedPoint.lean` (3 fates) | base-parametric tower constructor |
| `MoufangIntegerNormed213` (closed) | tower 구성을 typeclass argument로 받는 인터페이스 |

곱셈 구조 (cross-term bilinear, conjugation)는 모두 Lens 밖
(algebra-side); Algebra213 typeclass가 그 빈 공간을 메운다.

## ⏳ OPEN — next-session targets

### Phase 5 — SHIFT RULE 추상 functor
`shift_iso_L3` (구체 case-bash decide) 을
`[CommStarRing213 α] [CommStarRing213 β] → ...` parametric 정리로.

### Phase 6 — Base-parametric tower constructor
`def Tower (Base : Type) [MoufangIntegerNormed213 Base] : Nat → Type`
정의 → ∀-typed tower 추상.  Type A/B/C/D 자동으로 인스턴스.

### (math crux) Flexibility over a non-associative base — **CLOSED 2026-06-01**
The cross-pair is proved (`FlexAlt213.flex_cross_pair`, via the
alternating associator `left_alt_polar`/`right_alt_polar` + central
trace), `FlexAlt213 Cayley` registered (`Levels/CayleyFlexAlt213`), and
`SedenionHeavy.flexible` is now strict ∅-axiom (componentwise
`Cayley.flexible_re`/`flexible_im`).  The whole CayleyDickson category-D
backlog is empty.  The per-level "what dies / what survives" staircase
is bundled in `Tower/CDTower.CD_tower_flexible` (∅-axiom): the premise
chain `CommStarRing213 ⊃ StarRing213 ⊃ TraceNormed213(assoc) ⊃
FlexAlt213(alt)` aligns one-notch with `comm → assoc → alt → flexible`,
and flexibility is the invariant bridging the *single* rung
(Cayley→Sedenion) where the proof switches from `mul_assoc`-driven to
polarization-driven.

### Phase 7 — vertical re-indexing hypothesis (originating 2026-06-01)

> "cd tower의 1,2,3,4… 층이, 진짜 완전한 형태의 대수적 타워가 아닐
>  수도 있다. cd의 1층이 이 가상의 완전한 대수 타워의 2층일수도,
>  2,3,4층이 3,5,8층 뭐 이런식일수도, 심지어 한 방향으로 올라가는
>  타워가 아닐수도 있고." — Mingu Jeong 2026-06-01
> ("the CD tower's layers 1,2,3,4… may not be the *complete* algebraic
>  tower; CD layer 1 might be layer 2 of a hypothetical complete tower,
>  layers 2,3,4 might be 3,5,8…, and it might not even ascend in a single
>  direction.")

This is a **second axis** of the same "CD is a subset" insight, distinct
from the §"4-Type matrix" (horizontal/Base axis).  Phase 7 asks whether
the **vertical doubling index `n ↦ 2^n` is itself a subsample** of a finer
"complete" index.

**What the repo already grounds (horizontal + offset, SUPPORTED):**
  - CD-classical = Type-A *column* of the (Base × doubling) matrix; not a
    standalone whole (§"4-Type matrix", `TypeE_Rejection`).
  - All named towers (CD / universe-chain `5^L` / P-orbit / GRA /
    depth-ladder) are *one self-pointing orbit read through different
    Lenses* (`theory/essays/tower_atlas.md` lines 3–17): "not one
    direction" is the right shape — it is **one orbit, many readings**.
  - **Cross-column level offsets are real and LINEAR (+1):** SHIFT RULE
    identifies cells at *different level indices* — `shift_iso_L3`
    (A.L2 ≅ B.L3) and `SedenionOrder4Monopoly` (A.L5 ≅ B.L6).  The *same*
    algebraic object sits at level `n` in one column and `n+1` in
    another.  This is exactly the seed of "CD layer = layer f(n) of a
    finer object": the finer object is the SHIFT-iso **quotient** of the
    matrix, and each column embeds into it at a column-dependent offset.

**What is NOT yet grounded (vertical re-index, OPEN / partly refuted):**
  - The known offsets are **+1 linear**, not the user's *non-linear*
    `1,2,3,4 ↦ 2,3,5,8` (Fibonacci-shaped) guess.  No repo artifact
    supports a non-linear / golden vertical reindex of a *single* column.
    (The φ that appears — `Real213/Phi*`, `FibonacciCutoff` — is the
    *limit-ratio* of the asymptote, not a level index; `tower_atlas`
    lines 117–125 separate "Lens diagonal" from "P-orbit" precisely to
    block this conflation.)  So treat the Fibonacci form as **unsupported
    speculation** until a concrete iso is exhibited.
  - The honest open kernel is **global-rank consistency**, not Fibonacci:
    *does there exist a single rank `r : (Base, level) → ℕ` such that
    every SHIFT-iso cell-pair shares `r`, and CD-A maps into `r` as a
    not-necessarily-contiguous subsequence?*  If yes → "CD is a subsample
    of the complete tower (= image of `r`)", and the gaps in
    `r(A.level)` are the missing layers the user senses.  If the offsets
    are inconsistent under composition (A→B is +1 but A→C ≠ A→B + B→C),
    **no global linear rank exists → the complete tower branches**, which
    *supports* "not one direction" while *refuting* "simple subsequence".

**Concrete falsifiable probe (formalizable next step):**
  1. Enumerate the proven SHIFT isos as edges of a graph on cells
     `(Type, level)` (`shift_iso_L3`, `SedenionOrder4Monopoly`, +any in
     `Order4Monopoly_L{4,5,6}T`, `CayleyOrder4Monopoly`,
     `SedenionOrder4Monopoly`).
  2. Test whether the edges admit a consistent integer potential `r`
     (offsets compose: a `decide`-checkable finite condition on the known
     unit-loop order-distributions).
  3. If consistent: define `completeRank` and prove `CD-A ↪ image` is
     injective-non-surjective (the *subsample* statement) — and read off
     which `r`-values CD-A skips (the "missing layers").
  4. If inconsistent: exhibit the offending triangle — that *is* the
     proof the tower is not single-directional.

This is the formal successor to Phase 5 (SHIFT-RULE abstract functor):
the functor gives the edges; Phase 7 asks for the global potential they
do or do not admit.

### Phase 7.1 — conjecture catalog (marathon 2026-06-01)

**Pivotal reframe (the SHIFT edges are *unit-loop* isos, not algebra
isos).**  `shift_iso_L3` relates `ZI` (commutative) to `L3T`; if `L3T`
is the dim-4 quaternion-analog it is *non*-commutative, so they cannot be
isomorphic *as algebras* — the iso is at the **unit-loop** level (both
have order-4 unit loops).  Therefore the "hypothetical complete tower" is
most likely **not** a tower of algebras but the **spine of finite
Moufang loops** (the unit loops): `Z₂ ⊴ Z₄ ⊴ Q₈ ⊴ M₁₆ ⊴ M₃₂ ⊴ …`.  The
four algebra-Types are different **skins** (lattice realizations) over
one shared loop-spine; SHIFT edges are the fibers of the projection
`cell ↦ its unit loop`.  This is the precise form of "CD is a subset":
CD-A is one section of `(cell ↦ loop)`, hitting loop-spine positions that
another skin may fill differently.

Conjectures (status: G=grounded fragment exists, C=conjecture, ?=data-
dependent, pending the SHIFT-edge enumeration):

- **P7-A (loop-spine) [C].**  The SHIFT-iso quotient of the `(Type,level)`
  cell graph is a *linear* chain — the finite Moufang loop spine
  `M_{2^k}` (`Z₂,Z₄,Q₈,M₁₆=octonion loop,…`).  Every SHIFT edge connects
  cells with isomorphic unit loops; the rank `r(cell) := ` (loop position)
  is the canonical "complete-tower" index.
- **P7-B (global potential consistency) [C, THE decision point].**  The
  SHIFT offsets compose: there is `r : (Type,level) → ℕ` with `r` equal on
  every SHIFT-edge pair and strictly increasing in `level` within each
  column.  *Falsifier:* a non-closing triangle (A→B→C ≠ A→C offset).
  Decidable on the finite order-distribution data.  **If true → CD-A ↪
  image(r) is the subsample statement; if false → the spine branches
  (= "not one direction" proven, "simple subsequence" refuted).**
- **P7-C (offset linearity) [G partial: +1 twice].**  Current edges
  (`A.L2≅B.L3`, `A.L5≅B.L6`) give a constant `+1` A→B offset, i.e.
  `r(T,ℓ)=ℓ+c_T` *linear*.  Conjecture: it stays linear (no Fibonacci).
  The user's `1,2,3,4 ↦ 2,3,5,8` (non-linear) form is **predicted FALSE**
  unless an iso with a *varying* offset is exhibited — that single
  counterexample would flip P7-C and vindicate the non-linear guess.
- **P7-D (skin invariant) [?].**  What distinguishes the four skins over
  the shared loop at a given `r`?  Candidate: the *base discriminant*
  (`disc P`-type) — A: `x²+1` (disc −4), B: `x²−D`, C: `x²+x+1` (disc −3,
  Eisenstein), D: Hurwitz.  Conjecture: skins at equal `r` are
  unit-loop-isomorphic but algebra-distinguished by base discriminant /
  order-distribution refinement.  *Test:* a proven NON-iso of two
  same-dim cells in different columns (a distinguishing invariant).
- **P7-E (gap reading = missing layers) [C].**  If P7-B holds, the
  `r`-values that B/C/D realize but A skips are exactly the "missing
  layers" intuition.  Conjecture: Type C (Eisenstein, 3-element seed
  `(1,ω,ω²)`) realizes loop-spine positions *between* A's, because its
  seed is order-3 not order-2 — so C is the densest skin and A is the
  sparsest.  *This is the sharpest read of "CD layer 1 = layer 2 of the
  complete tower": A is a sparse section, C a denser one, of the same
  spine.*

**Decision point of the whole marathon = P7-B** (decidable).  Plan:
enumerate edges → encode order-distributions as concrete Nat data →
`decide` the potential-consistency condition → either build `completeRank`
+ prove `CD-A` non-surjective into it (P7-E gaps), or exhibit the
branching triangle.

### Phase 7.2 — proven (∅-axiom) `meta_tower_loop_spine`

`Tower/MetaTowerLoopSpine.meta_tower_loop_spine` (strict ∅-axiom,
assembled from the per-level order distributions, no expensive
re-decide).  Empirical inputs now pinned (all `decide`, file:line):
`shift_iso_L3` (`ZSqrtMinus2Findings:53`), `cay/sed_order_distribution`
(`Levels/{Cayley,Sedenion}Order4Monopoly`), `L5T/L6T_order_distribution`
(`Tower/Order4Monopoly_L{5,6}T`), `typeC_cyclotomic_3_preserved`
(`UniversalOrderGrowthC:31`).  The dyadic order-4 counts are
`g(p) = 2^{p+1} − 2`: `Z₂`0, `Z₄`2, `Q₈`6, `M₁₆`14, `M₃₂`30.

Resolved conjectures:
  - **P7-A loop-spine [CONFIRMED, dyadic branch].**  Order distribution
    `= ` unit-loop class; `Cayley(A,dim8) ≅ L5T(B,dim16)` (`M₁₆`),
    `Sedenion(A,dim16) ≅ L6T(B,dim32)` (`M₃₂`).  spine ≠ dimension.
  - **P7-C offset linearity [CONFIRMED +1].**  Two independent rungs give
    the same `+1` B-over-A offset.  **The Fibonacci/non-linear guess is
    REFUTED** for the dyadic branch.
  - **P7-E subsample/gap [CONFIRMED].**  At equal dim 16,
    `Sedenion(M₃₂) ≠ L5T(M₁₆)` — Type A indexes the spine `n ↦ n+1`,
    skipping the bottom `Z₂` rung that B's `ℤ[√-2]` fills.  *This is the
    exact formal content of "CD layer n = layer n+1 of the complete
    tower".*
  - **P7-D branch [CONFIRMED first half].**  Dyadic (A) carries no
    3-torsion; Eisenstein (C) does → the spine branches by base
    discriminant.

Still open after Phase 7.2:
  - **P7-B (global consistency across ALL columns, incl. C/D).**  Proven
    consistent on the A–B dyadic edges; the full potential over the
    branched graph (Eisenstein, Hurwitz) is not yet bundled.
  - **No cross-branch iso (dyadic ↔ Eisenstein)** is an *untested
    absence*, not a theorem — needs a distinguishing-invariant proof
    (3-torsion present/absent is the candidate witness).
  - **Parametric `Tower (Base) (n) : Type`** + abstract SHIFT functor
    (the long-standing Phase 5/6) — would make `r` a definition, not a
    per-cell `decide`.
  - **asymptote ↦ branch:** `asymptote_ab` is `(2,0)` for A *and* B (same
    dyadic branch) but `(5,−1)` for C, `(1,1)` for D — conjecture: the
    `ℤ[√5]` asymptote is the branch (discriminant) invariant, *constant
    along columns, varying across branches* — linking P7-D to
    `Mobius213CDBridge.cd_mobius_bridge_master`.

### Phase 7.3 — adversarial review integrated (marathon 2026-06-01)

Critique pass (second agent) confirmed the proofs sound but corrected the
*interpretation*; two honesty fixes and two new ∅-axiom theorems:

**Honesty corrections (carried into the Lean docstrings):**
  - **basis loop ≠ arithmetic unit group.**  `cay_units` is the
    16-element ±basis-doubling Moufang loop (`lip_units.map cay_left ++
    … cay_right`), *not* the 240-unit integer-octonion group (E₈ roots).
    The `Cayley ≅ L5T` alignment is an iso of *basis loops*; for the full
    240/… unit groups it likely **breaks** (different base lattices give
    different root counts).  So "A and B realise the same *algebra* one
    rung apart" is **unsupported** — only the basis-loop relation holds.
    Drop "the octonion unit loop" phrasing.
  - **`+1 offset` is partly a naming artifact.**  There is no
    column-intrinsic level index; the naming-free content is the
    *equal-dimension* loop difference (`Sedenion ≠ L5T` at dim 16,
    `Cayley ≠ L4T` at dim 8).  "n ↦ n+1" is a description of that single
    gap, not an independent fact.  Likewise the dyadic order-4 count is
    the closed form `2·dim − 2` (all non-`±1` units have order 4), so the
    within-dyadic "spine" is the seed unit count re-told.
  - **rank, not disc.**  The asymptote classifier is
    `rank = ω(unitOrder) − 1 + nonAbelian` (`AlgebraTowerAsymptote`),
    *not* a base discriminant routed through the Möbius `disc P = 5`
    (a different 5 = `tr²−4det`).  `cd_mobius_bridge_master` ties only the
    C/D asymptotes to P-invariants, never the dyadic `(2,0)`.  So P7-D
    should read **branch ⇔ rank ⇔ asymptote**, not "skin = base disc".

**New proven (∅-axiom, `Tower/MetaTowerLoopSpine`):**
  - `no_cross_branch_loop_iso` (NC-1): order-3 count `= 0` on dyadic
    basis loops, `= 2` on Eisenstein — the named obstruction to any
    orderOf-preserving (hence any loop) iso across branches.  The
    branches also separate by the order-4 *sequence* (`6,14,30` vs
    `6,18,42`), so the separation is twofold.
  - `asymptote_classifies_branch` (NC-4): `asymptote_ab` constant on the
    dyadic branch (`A = B`, blind to the A↔B column shift) and distinct
    across the three branch classes.

**Still open (sharpened):**
  - NC-2 — **CONFIRMED.**  `dyadic_branch_bottom_rung` formalises the
    `Z₂` bottom: `ℤ[√-2] = ZSqrt 2` has unit group `{±1}` (2 units, no
    order-4, no 3-torsion), one doubling below Type A's base `ℤ[i]` (`Z₄`,
    4 units, order-4 count 2).  So "Type A skips the bottom rung" is now a
    theorem, not a caveat — the dyadic spine extends below Type A and
    Type A indexes it from the second position.
  - NC-3 — "C is the densest branch": order-4 count strictly greater at
    each dim (`18>14`, `42>30`); decidable per level, conjectural for all.
  - NC-5 — completion = a **branching forest rooted at `Z₂`** (dyadic
    spine `Z₂◁Z₄◁Q₈◁M₁₆◁…`, Eisenstein `Z₂◁Z₆◁Dic₃◁…`, Hurwitz), not a
    single chain and not a Fibonacci re-index of one column.  Only its
    finite shadows (NC-1..4) are ∅-axiom-accessible; the forest object
    itself needs the parametric `Tower (Base)` constructor (Phase 6).

**Marathon verdict on the originating intuition:** "CD is not the
complete tower / layer n = layer n+1 / not one direction" is **confirmed
and formalised** at the basis-loop level; the non-linear (Fibonacci)
re-index is **refuted**; the honest completion is a discriminant-branching
forest, whose finite shadows are now ∅-axiom theorems.

### Phase 8 — seed-`μ` governance (the imaginary-quadratic-units thread)

The numbers from Phase 7 point past "branching forest" to *what indexes
the branches*.  Seed unit counts: `ℤ[√-2]` = 2, `ℤ[i]` = 4, `ℤ[ω]` = 6,
Hurwitz = 24.  Per-level counts: Type A `= 2·dim`, Type B `= 1·dim`,
Type C `= 3·dim`; order-4 counts: dyadic `2·dim − 2`, Eisenstein
`3·dim − 6`.  **Classical fact:** the only imaginary quadratic fields
with units past `{±1}` are `ℚ(i)` (`μ₄`, 4 units) and `ℚ(ω)=ℚ(√-3)`
(`μ₆`, 6 units); every other imaginary quadratic order has `μ₂ = {±1}`.
So the meta-tower's columns look governed by the seed's **root-of-unity
group `μ`**, with `ℤ[i]`, `ℤ[ω]` the two exceptional dense columns.

Conjectures (status `?` pending the Phase-8 data + math agents):

- **P8-A (`μ` governs density).**  Per-level unit count `= (|μ_seed|/2)·dim`;
  density `c = |μ_seed|/2 ∈ {1,2,3}` for `μ ∈ {μ₂,μ₄,μ₆}` (B, A, C).
  *Formalizable:* the `c·dim` law from the unit-doubling theorems.
- **P8-B (`μ` odd-torsion governs branch).**  Loop-spine torsion menu =
  the 2-power torsion (always) plus the **odd part of `μ_seed`**: `μ₂,μ₄`
  give 2-power only (dyadic); `μ₆` adds `3,6`-torsion (Eisenstein).  So
  *branch = whether `3 ∣ |μ_seed|`*.  Grounded already by
  `no_cross_branch_loop_iso` (order-3: 0 vs 2).
- **P8-C (exceptional columns).**  Among imaginary quadratic seeds,
  exactly `ℤ[i]` and `ℤ[ω]` are dense (`c>1`); all `ℤ[√-D]` (`D≥2`) are
  density-1 generic dyadic.  This is the CD-tower shadow of the `μ₄/μ₆`
  exceptionality.  *Formalizable only as the finite trichotomy
  `|μ_seed| ∈ {2,4,6}`; the "only these" is a field-theory fact, not a
  decide.*
- **P8-D (Hurwitz = Eisenstein-containing, rank 2).**  `2T` (Hurwitz, 24
  units, element orders `{1,2,3,4,6}`) contains `μ₆` (`ω ∈` Hurwitz), so
  its torsion menu `⊇` Eisenstein's; it is a **quaternion (rank-2)** seed,
  the "next dimension of seed".  Conjecture: Type D's spine contains the
  Eisenstein spine.  *Test:* does Hurwitz have order-3 units (`>0`)?
- **P8-E (closed forms).**  order-4 count `= c·dim − k`, with `k` = the
  non-order-4 units (`±1` plus the cyclotomic surplus): dyadic `2·dim−2`
  (`k=2`), Eisenstein `3·dim−6` (`k=6 = 2 + 2·(order-3) + 2·(order-6)`).
  *Formalizable per level; the closed form is the conjecture.*

**The deeper object (P8 candidate completion).**  The "complete tower"
is the **family of CD towers over imaginary quadratic (and quaternion)
orders, fibered by the unit group `μ`** — classical CD = the `ℤ[i]`
column; the special columns (`i`, `ω`, and the quaternionic `2T`) are the
CM-exceptional points with extra automorphisms.  `μ ∈ {2,4,6}` (plus `2T`
for the rank-2 lift) is the organizing trichotomy.  Decidable shadows:
the density `c·dim` law, the order-4 closed forms, and `branch = 3∣|μ|`.

### Phase 8.2 — confirmed (∅-axiom) + the deep structure

Two agents (repo data + imaginary-quadratic math) confirmed the data and
synthesized the structure.  Proven in `Tower/SeedUnitGovernance` +
`Tower/MetaTowerLoopSpine`:

  - `seed_unit_trichotomy` — `|μ| = 2,4,6,24` for `ℤ[√-2], ℤ[i], ℤ[ω],`
    Hurwitz.  **P8-A/C confirmed** (rank-1 trio `{2,4,6}`).
  - `eisenstein_seed_unit_count_eq_NS_NT` — `|μ_{ℤ[ω]}| = 6 = NS·NT`.  The
    exceptional dense rank-1 seed's unit count *is* the atomic product
    (`ZOmegaUnits.units_count_eq_NSNT`).
  - `branch_by_odd_torsion` — order-3 count `0 / 0 / 2 / 8` for A / B / C /
    Hurwitz.  **P8-B confirmed**: branch `= (3 ∣ |μ|)`.
  - `hurwitz_contains_eisenstein_core` — `2T` carries order-3 (8) *and*
    order-6 (8): the Eisenstein menu `{3,6}` (`μ₆ ⊂ 2T`).  **P8-D
    confirmed**: Eisenstein is the abelian core of the rank-2 Hurwitz
    branch.
  - `seed_density_at_dim8` — at dim 8 the columns carry `2·8, 1·8, 3·8`
    units (densities `c = |μ|/2 = 2,1,3`).  **P8-A density confirmed.**
  - Data also pins (file:line, all `decide`): A `=2·dim`, B `=1·dim`
    (to `L9T=256`), C `=3·dim`; order-4 `2·dim−2` (dyadic) / `3·dim−6`
    (Eisenstein); Hurwitz order distribution `(1,1,8,6,8)` for
    `{1,2,3,4,6}`.

**The deep structure (math synthesis — the real answer to "complete
tower").**  Density `c = |μ/{±1}|` (projectivized unit order); branch =
the *odd torsion* of `μ`.  The trichotomy is **forced**: imaginary
quadratic fields with `μ ≠ {±1}` are *exactly* `ℚ(i)` (`μ₄`) and `ℚ(ω)`
(`μ₆`) (Dirichlet, rank 0).  So `ℤ[i], ℤ[ω]` are the two exceptional
columns *for the identical reason* they are the only such fields.

  - **`A/B` = one branch, index-shifted**: `μ₄`'s built-in `i`
    pre-supplies one CD doubling, so `ℤ[i]` realises the dyadic spine at
    half the dimension of generic `ℤ[√-D]` — same loop sequence, density
    2 vs 1, index `n ↦ n+1`.  (`μ₄` is a 2-group ⇒ stays dyadic.)
  - **branch = seed-lattice symmetry**: `μ₂, μ₄, μ₆` = `Aut` of the
    rectangular / square / **hexagonal** rank-2 lattice.  The hexagonal
    3-fold symmetry *is* the order-3/6 torsion of branch C.  Odd torsion
    a CD doubling can never manufacture from `{±1}` and `√-1` — which is
    why Eisenstein is a genuinely new branch, not a shifted dyadic one.
  - **`2T` (Hurwitz) = rank-2 lift**: the `24`-cell / `D₄`–`F₄`
    symmetry; `μ₆ ⊂ 2T` makes Eisenstein the abelian core, the non-abelian
    quaternionic completion `Q₈⋊C₃` on top (the asymptote `nonAbelian`
    flag, rank 2).
  - **The complete object**: the meta-CD-tower is a **functor from finite
    unit groups of definite `ℤ`-orders** (= finite subgroups of the
    division-algebra units: `μ₂,μ₄,μ₆` rank-1; `2T,…` rank-2) **to graded
    systems of basis-unit Moufang loops**.  Classical CD = the section
    over the trivial seed `μ = {±1}` (the density-1 dyadic trunk).  The
    speculative endpoint: the **binary-polyhedral / McKay (ADE) ladder**
    — `μ₄,μ₆` cyclic, `2T` the first binary polyhedral; `2O (48), 2I
    (120)` would be the next exceptional seeds.  The CM `j`-invariant
    connection is real but downstream — the operative invariant is
    `Aut(E) = μ_seed`, not the full CM datum.

**Marathon-2 verdict:** the originating "complete tower" is the family of
CD towers **fibered over seed unit groups**; the `μ ∈ {2,4,6}` trichotomy
(Dirichlet) makes `ℤ[i], ℤ[ω]` the two exceptional dense columns, branch
`= 3∣|μ| =` hexagonal seed-lattice symmetry, and Hurwitz `2T` the rank-2
lift containing Eisenstein.  Decidable shadows are all ∅-axiom.  Open
frontier: the rank-2 (`2O, 2I`) seeds and the McKay/ADE classification.

### Phase 8.3 — adversarial critique integrated (honest status)

A third agent stress-tested the Phase-8 theorems.  Soundness: all
∅-axiom, true `decide`/composition facts.  The critique was about *what
the decidable facts mean* — corrections applied to the Lean docstrings:

  - **Density-governance is largely a restatement of the construction.**
    The tracked object is the *doubled-basis loop* (`lip_units.map
    cay_left ++ … cay_right`), twice the previous by construction; so
    "density `= |μ|/2`" is the seed count read back out, not independent
    governance.  The *contentful* claim is **branch** (odd torsion).
  - **Branch is the real content** — 3-torsion is a genuine iso invariant
    the doubling *preserves but cannot create*.  `branch_by_odd_torsion`
    now covers **every measured dyadic cell** (`lip,cay,sed,L4T,L5T` →
    order-3 `= 0`) vs `zod = 2`, `hur = 8`.  But the universal direction
    ("no dyadic level *ever* gains odd torsion") is still **pointwise**,
    not a uniform theorem (would need the parametric tower).
  - **`6 = NS·NT` is a coincidence as formalized** — the same `6` is also
    `3!`, `d+1`, ….  The structural reading (`μ₆ ≅ μ₂×μ₃` ↔ the `K_{3,2}`
    ST-phase `μ_NT × μ_NS`) is real but **not wired** in Lean.  Docstring
    demoted to numerical identity.
  - **`hurwitz_contains_eisenstein_core` → `hurwitz_carries_cyclotomic_torsion`.**
    Count `> 0` does *not* witness a subgroup `μ₆ ⊂ 2T`, and `2T`'s
    3-torsion (8) is 4× a single `μ₆` (2); `2T ≅ SL(2,𝔽₃)` non-abelian.
    Docstring now states only the order-count menu overlap.
  - **Number-theoretic labels** (the trichotomy uniqueness; lattice
    symmetry `μ₂/μ₄/μ₆` = rectangular/square/hexagonal; the McKay/ADE
    ladder; the loop-class names `Q₈/Dic₃`) are **classical facts or
    speculation, cited not formalized** — they live in this note, and the
    Lean docstrings now say so.

**Net honest status of "seed-`μ` governs the tower":** the *density*
half is a corollary of the doubling; the *branch* half (odd-torsion =
discriminant class) is the genuine, partly-formalized content; the
*deep* identifications (lattice symmetry, McKay, CM) are the cited
mathematical frame, the right picture but beyond the ∅-axiom finite
shadows.  Hardening targets left: a real `μ₆ ⊂ 2T` subgroup witness
(generator + closure), the CRT `μ₆ ≅ μ₂×μ₃` wired to `(NT,NS)`, and the
uniform "dyadic doubling preserves order-3 `= 0`" (needs the parametric
`Tower (Base)` constructor — the standing NC-5 frontier).

### Phase 8.4 — the two cited claims hardened into proofs (marathon-3)

Both overclaims the critique flagged are now ∅-axiom theorems in
`Tower/SeedUnitGovernance`:

  - **`mu6_subgroup_of_2T`** — a genuine cyclic `μ₆ ⊂ 2T`.  The Hurwitz
    unit `g = ⟨1,1,1,1⟩ = (1+i+j+k)/2` is a primitive 6th root
    (`hur_orderOf g = 6`, indeed `g³ = -1`); its 6 powers
    `{1,g,g²,g³,g⁴,g⁵}` are distinct and all lie in `hur_units`.  So the
    subgroup containment is *witnessed*, not inferred from counts —
    `2T`'s order-3 count 8 is still 4× a single `μ₆`, but a `μ₆` is now
    provably inside.
  - **`eisenstein_units_crt`** — `μ₆ ≅ μ_NT × μ_NS` by CRT.  `{±1}`
    (order `NT=2`) × `{1,ω,ω²}` (order `NS=3`); the product map
    `(s,t) ↦ s·t` is a `Nodup` bijection onto `units6`.  So `6 = NS·NT`
    is the *structural* `μ_NS × μ_NT` split, not a numerical collision —
    the order-2 factor is the `±1`/temporal `NT`, the order-3 factor the
    cube-root/spatial `NS`.

**McKay-ladder evidence found in-repo (not external after all).**
`Lib/Math/Geometry/AlgebraicGeometry.lean` already carries the rank-2
continuation past Hurwitz: `SL(2,𝔽₅) ≅ 2I` (binary icosahedral, 120),
"`Type D` (Hurwitz `2T`, 24) is the `ℤ`-base level; icosian (`2I`, 120)
extends to `ℤ[φ]` (`Type E`)", with `24·5 = 120` and `5·4·6 = 120`
(`algebraic_geometric_core`).  So the seed ladder `μ₄,μ₆ → 2T → 2I`
(cyclic → binary tetrahedral → binary icosahedral) is the repo's own
`A/C → D → E` progression, the `ℤ[φ]` golden seed being the next
exceptional column.  The McKay/ADE frame for the "complete object" is
thus *gestured by the repo*, not merely imported — though `2I`/`ℤ[φ]`
unit-group constructions are cited, not yet built.

**Marathon-3 verdict:** the two formalization gaps the adversarial pass
exposed are closed (`μ₆ ⊂ 2T` and `μ₆ ≅ μ_NT×μ_NS` both proven), making
`6 = NS·NT` structural and the Hurwitz–Eisenstein containment genuine.
The seed-`μ` ladder extends in-repo toward `2I/ℤ[φ]` (Type E), pointing
the "complete object" at the binary-polyhedral/McKay classification.

## 메타 원칙 (CLAUDE.md 보완)

> **크게 생각하고 레포지토리를 먼저 뒤져라.**
> 대부분의 직관은 코드베이스 어딘가에 이미 부분 형식화돼 있다.
> 4-row 타워 매트릭스, SHIFT RULE, Type C ZOmega tower — 모두
> 사용자가 처음 직관으로 제시한 게 이미 존재했다.

— Mingu Jeong (2026-05-29 GRA × CD 메타-타워 대화 중)
