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

### Phase 9 — Type E (`ℤ[φ]` icosian, `2I`, 120) — the order-5 branch

The next ladder rung past Hurwitz (`2T`, 24) is the **icosian ring** —
the maximal order of the quaternion algebra over `ℚ(√5)`, unit group the
**binary icosahedral group `2I ≅ SL(2,𝔽₅)`** of order 120.  Its element
orders are `{1,2,3,4,5,6,10}` — so it carries **order-5 and order-10
torsion absent from every lower seed** (`A/B/C/D` menus top out at 6).
This is the genuinely *new* branch: the golden/pentagonal signature.

Conjectures:

- **P9-A (order-5 torsion is the Type E signature) [decidable witness].**
  An explicit icosian unit of order 5 exists.  Construction (computed):
  over `ℤ[φ]` (`φ²=φ+1`, element `⟨a,b⟩ = a+bφ`), quaternions with
  `ℤ[φ]` coordinates scaled by 2 (Hurwitz-style); the unit
  `g = ((φ-1)+φ·i+j)/2` has `normSq = ((φ-1)²+φ²+1)/4 = 1` and real part
  `(φ-1)/2 = cos 72°`, so `g⁵ = 1`, `g ≠ 1` ⇒ order exactly 5.  Witnesses
  Type E carries 5-torsion.
- **P9-B (the seed ladder = binary polyhedral / McKay).**  The seeds form
  `μ₂ ⊂ μ₄ ⊂ μ₆` (cyclic) `→ 2T (24) → 2I (120)` — the binary polyhedral
  groups, the `A–D–E` McKay classification of finite `SU(2)` subgroups.
  Density / branch governance extends: `2I` adds the order-5 (`A₄`-free
  icosahedral) torsion.  `24·5 = 120` (`AlgebraicGeometry.algebraic_geometric_core`)
  is the `2T → 2I` index.
- **P9-C (`5 = NS+NT` floor meets `2I`) [speculative].**  `2I`'s order
  `120 = 5! = (NS+NT)!`, and the icosian ring lives over `ℚ(√5)` with
  `5 = disc P = NS+NT` (the Möbius/atomic floor).  Conjecture: Type E is
  where the seed ladder *meets the `5`-floor* — the golden seed `ℤ[φ]`
  is the CM/automorphism shadow of the same `P = [[2,1],[1,1]]`,
  `disc 5`, that bottoms the depth-ladder and the CD asymptote.  (Links
  `tower_atlas` `5`-floor to the McKay endpoint.)

Decidable target: P9-A (the order-5 icosian witness).  Stretch: the full
`2I` order distribution; P9-B/C are the cited frame.

### Phase 9.2 — P9-A confirmed: the order-5 icosian unit (∅-axiom)

`Tower/TypeEIcosian.icosian_order5_unit` (strict ∅-axiom).  Built from
scratch (the repo had no `ℤ[φ]` ring, no quaternion-over-ring, no icosian
— only the textual `SL(2,𝔽₅) ≅ 2I`):
  - `ZPhi` golden integers `⟨a,b⟩ = a+bφ`, `φ²=φ+1`, `(a+bφ)(c+dφ) =
    (ac+bd)+(ad+bc+bd)φ`;
  - `Icosian` = quaternions with `ℤ[φ]` coords, scaled-by-2 (Hurwitz
    convention with `ℤ[φ]` for `ℤ`);
  - `g = ((φ-1)+φ·i+j)/2 = ` scaled `⟨φ-1,φ,1,0⟩`: `normSq g = 4` (a
    unit), `g⁵ = 1`, `g ≠ 1` ⇒ order exactly 5 (5 prime).
  - `g` is an *even* permutation of `(0,1/φ,1,φ)/2` (a 3-cycle), hence one
    of the 96 golden icosians — a genuine element of `2I`.  The
    `decide` passing through `Int /2` halving also *self-certifies* the
    construction: a non-icosian `g` would break `g⁵ = 1` under
    truncation.

This is the **first executable order-5 element in the repo** and the
McKay rung past `2T` — order-5 torsion no lower seed carries.

**Honest scope (reconciling `Misc/TypeE_Rejection`).**  `Misc/TypeE_Rejection`
excludes the icosian from the strict 4-row `ℤ`-coefficient CD matrix, and
correctly so: `ℚ(√5)` is *real* quadratic, so `ℤ[φ]`'s *own* unit group is
*infinite* (`φ` fundamental).  Phase 9 does **not** contradict this — it
steps deliberately *outside* the `ℤ`-CD scope: the relevant finite object
is the *totally-definite quaternion order* over `ℤ[φ]`, whose unit group
*is* finite (`2I`, 120).  So Type E is "rejected as a `ℤ`-CD seed,
realised as the rank-2 McKay rung over `ℤ[φ]`" — two compatible facts.
P9-C (`120 = 5! = (NS+NT)!`, icosian over `ℚ(√5)`, `5 = disc P = NS+NT`)
remains a *speculative* link of the seed-ladder endpoint to the repo's
`5`-floor, not formalized.

### Phase 9.3 — adversarial critique integrated

An agent independently re-implemented `ZPhi`/`Icosian.mul` and recomputed
`g²…g⁵` in exact `ℤ[φ]`: all three original conjuncts reproduce, build
clean, genuinely ∅-axiom.  Crucially it found that **no truncation ever
occurs** on the `g` orbit (every pre-halving coordinate of `g²…g⁵` is
even), so the `Int /2` halving is exact throughout and `normSq` (computed
*without* halving) is a clean unit witness — the construction is sound,
not a truncation artifact.  The two soft spots it flagged were rhetorical,
both now fixed:

  - **order exactly 5 promoted to theorem.**  Added `g5² ≠ 1` so
    `icosian_order5_unit` proves order divides 5, `≠ 1`, `≠` order-2 —
    the "exactly 5" no longer lives only in prose.  (Order-10 witness
    `icosian_order10_unit` added in parallel: full `{5,10}` menu.)
  - **the `orderOf`-vacuity closed.**  `two_T_torsion_bounded_at_6`:
    `hur_orderOf` returns `0` exactly for orders outside `{1,2,3,4,6}`,
    and `hur_order_distribution` proves that `0`-count is `0` — so `2T`
    *provably* has no order-5/order-10 element.  The contrast "Type E
    carries `{5,10}`, the lower seeds do not" is now a real theorem, not
    an artifact of a checker that never tests the 5th power.
  - **framing softened.**  The Lean docstring now says "an order-5 element
    *of the icosian quaternion order*" (not "of `2I`", which would
    presume the 120-group), marks the "McKay rung" reading as conjectural
    narrative, and states that only the explicit elements — not the full
    `2I` group, its closure, or P9-B/C — are proved.

**Marathon-4 verdict:** the seed/McKay ladder now has executable
witnesses at its `2I` rung — order-5 and order-10 icosian units over
`ℤ[φ]`, with the lower-seed order-bound proved so the new pentagonal
torsion is genuine.  The construction is honestly scoped (one/two
elements, not the 120-group; `ℤ[φ]` coefficients outside the `ℤ`-CD
matrix), and the McKay/ADE "complete object" remains the cited frame the
repo's own `24·5=120`, `SL(2,𝔽₅)≅2I` point toward.

### Phase 9.4 — the `E₆–E₇–E₈` exceptional trio completed (`2O`, marathon-5)

`Tower/TypeOOctahedral` adds the missing middle rung — the **binary
octahedral group `2O` (48, `E₇`)** — completing the binary-polyhedral /
McKay exceptional trio as definite quaternion orders over the three
relevant rings:

| group | order | ring | new torsion | McKay |
|---|---|---|---|---|
| `2T` | 24 | `ℤ` (Hurwitz) | `3,6` | `E₆` |
| `2O` | 48 | `ℤ[√2]` | `8` | `E₇` |
| `2I` | 120 | `ℤ[φ]=ℤ[√5]` | `5,10` | `E₈` |

The clean parallel: `2T` over `ℤ`; `2O`, `2I` over the *real* quadratic
rings `ℤ[√2]`, `ℤ[√5]` (own units infinite, definite-order units finite).
Built `ZRt2` (`(√2)²=2`, `mul ⟨a,b⟩⟨c,d⟩ = ⟨ac+2bd, ad+bc⟩`) + `ℤ[√2]`-
quaternions, and proved (∅-axiom):
  - `octahedral_order8_unit` — `g = (1+i)/√2 = cos 45° + sin 45°·i`,
    scaled `⟨√2,√2,0,0⟩`: `normSq = 4` (unit), `g⁸ = 1`, `g⁴ ≠ 1` ⇒ order
    exactly 8.  The octahedral `E₇` signature.
  - `two_T_has_no_order_8` — `2T` orders `⊆ {1,2,3,4,6}`, so order-8 is
    genuinely new at `E₇` (and absent from `2I`'s `{1..6,10}` too).

So the exceptional `E`-series now has executable order-witnesses at every
rung: `E₆` (`2T`, `{3,6}`), `E₇` (`2O`, `{8}`), `E₈` (`2I`, `{5,10}`).
Same honest scope as Phase 9.2/9.3 (explicit elements, not the full
48-/120-groups; the McKay/ADE identification is the cited frame).

**Marathon-5 verdict:** the seed ladder's exceptional endpoints
`E₆–E₇–E₈ = 2T–2O–2I` over `ℤ, ℤ[√2], ℤ[√5]` are all realised with
∅-axiom torsion witnesses (`{3,6} / {8} / {5,10}`).  The "complete
object" — finite unit groups of definite arithmetic orders, indexed by
the binary-polyhedral / McKay classification — now has concrete proven
shadows across its whole exceptional row, with the lower-rung order-bounds
proved so each new torsion type is genuine, not a checker artifact.

### Phase 10 — the loop closes: `P` meets the icosian `E₈` endpoint (marathon-6)

`Tower/MobiusPIcosian` ties the whole meta-CD-tower exploration back to
the DRLT *core*.  The framework's atomic Möbius generator
`P = [[2,1],[1,1]]` — trace `3 = NS`, det `1`, disc `5 = NS+NT` (the
floor that bottoms the depth-ladder, the CD asymptote, and the atomic
forcing) — reduced mod `5` is an **order-10 element of `SL(2,𝔽₅) ≅ 2I`**,
the binary-icosahedral `E₈` rung whose order-5/10 torsion the icosian
`g5`/`g10` witness over `ℤ[φ]`.

  - `P_mod5_order_exactly_10` (∅-axiom): via the existing `pellCoeff`
    Cayley–Hamilton detector for `M = [[2,1],[1,1]]`, `P¹⁰ ≡ I` while
    `P¹,P²,P⁵ ≢ I` ⇒ order divides 10, is none of `1,2,5`, hence exactly
    10.  `det P = 1` puts `P mod 5 ∈ SL(2,𝔽₅)`; `10 = NT·(NS+NT)`.
  - `mobius_P_meets_icosian_endpoint` bundles the `5`-floor invariants,
    the order-10 reduction, and `10 = NT·(NS+NT)`.

So the `5`-floor generator of the entire framework is the order-10
element of the seed ladder's `E₈` endpoint — the meta-CD-tower's top
rung and the foundational `P`-orbit are the *same* order-10 conjugacy
class in `2I`.  Honestly scoped: the group iso `SL(2,𝔽₅) ≅ 2I` and the
`P ∼ g10` conjugacy are cited classical facts; what is *proved* is `P mod
5`'s matrix order and its `SL(2,𝔽₅)` membership.

### Phase 11 — the complete object named: the full McKay `A–D–E` (marathon-7)

`Tower/MckayADECensus` makes the "complete object" explicit.  The finite
subgroups of `SU(2)` are McKay-classified into `A` (cyclic), `D` (binary
dihedral), `E₆,₇,₈` (`2T,2O,2I`) — and these are *exactly* the loop
classes the seed ladder realises:

| McKay | group | meta-CD-tower realisation |
|---|---|---|
| `Aₙ` | `Cₙ` | seed roots of unity `μ₂,μ₄,μ₆` (`units6 = C₆`) |
| `Dₙ` | `Dicₙ` | `Q₈ = Dic₂` (dyadic `Lipschitz`/`Cayley` loop), `Dic₃` (`ZOmegaDouble`) |
| `E₆` | `2T` | `Hurwitz` (24) |
| `E₇` | `2O` | octahedral over `ℤ[√2]` (48) |
| `E₈` | `2I` | icosian over `ℤ[φ]` (120) |

`mckay_ADE_census` (∅-axiom) bundles one discriminating order-signature
per family/rung: `A` (`|units6| = 6`, cyclic `C₆`); `D` (`Q₈` —
`Lipschitz` order-4 count 6; `Dic₃` — `ZOmegaDouble` order 12, 3-torsion
2); `E` (`2T` order-6 count 8; `2O` order-8 unit `g8`; `2I` order-5/10
units `g5,g10`).  The group-name identifications are the cited McKay
frame; the order signatures are proved.

So the "complete tower" the sparse-section intuition reached for is the
**McKay `A–D–E` classification of finite `SU(2)` subgroups** — every type
realised as a meta-CD-tower loop class, and (Phase 10) the `E₈` top
anchored to the framework's own `5 = NS+NT` floor via `P mod 5`.

**Marathon-6 verdict / arc close:** the six-marathon arc that began from
"CD is not the complete tower" closes a full circle — CD is a sparse
section of a discriminant-branching basis-loop spine (M1); the branches
are governed by the seed unit group `μ` (M2, hardened M3); the exceptional
`E₆–E₇–E₈ = 2T–2O–2I` rungs are realised with order-`{3,6}/{8}/{5,10}`
witnesses (M4–M5); and the `E₈` endpoint is generated, mod the `5`-floor,
by the framework's own atomic `P` (M6).  The "complete object" the
intuition reached for is the McKay-indexed family of finite definite-order
unit groups, with its top rung pinned to the DRLT `disc P = 5 = NS+NT`
floor.  All finite shadows ∅-axiom; the group-theoretic / CM frame
honestly cited throughout.

### Phase 12 — the three open frontiers worked (marathon-8)

The frontiers named at the arc close, now addressed:

  - **Full group closure.**  `Tower/FullOctahedral` proves the *complete*
    48-element `2O` order census `{1:1,2:1,3:8,4:18,6:8,8:12}` (the
    correct distribution — the 12 order-8 elements are the octahedral
    extras *with* a real part, `(1+i)/√2`; the 12 *without* join the
    6 `±eᵢ` at order 4).  The complete `E₇` rung, not just a witness.
    `Tower/FullIcosian` proves the `2I` order *spectrum* `{1,2,3,4,5,6,10}`
    via an explicit unit of each order.  (`2T`'s full census is the
    existing `hur_order_distribution`.)  The full 120-element per-order
    *count* census for `2I` needs the exact even-permutation/sign
    enumeration of the 96 golden icosians over `ℤ[φ]` + a heavy `decide`
    — deferred; the spectrum is proved.
  - **Parametric tower.**  `Tower/CDTowerParametric` defines the
    type-level `CDTowerType α n` (`CDDouble` is a bare pair, so the TYPE
    iterates with no instances) and proves the one-step parametric law
    (`conj` anti-distributive on `CDDouble α` for any `StarRing213 α`).
    The obstruction is made explicit: no uniform `∀ n, C (CDTowerType α
    n)` instance exists, since `CDDouble` drops commutativity (at
    `Lipschitz`) then associativity (at `Cayley`) — which is *why* the
    tower is studied rung-by-rung.
  - **`A`/`D` infinite families.**  `Tower/McKayADClosure` lifts the
    cyclic `A` and binary-dihedral `D` nodes from order-signatures to
    *closed groups*: `units6 = ⟨ζ₆⟩ ≅ C₆` (the six powers enumerate it),
    and `Q₈` (8 `Lipschitz` units) and `Dic₃` (12 `ZOmegaDouble` units)
    are each closed under `*`.

So the McKay `A–D–E` realisation now has: `A` (cyclic group `C₆`), `D`
(closed `Q₈`, `Dic₃`), `E₆` (`2T` full census), `E₇` (`2O` full
48-census), `E₈` (`2I` full order spectrum) — every family a proven
group/census shadow, only the `2I` 120-count deferred.

### Phase 12.1 — the `2I` count, ripe (heaviness = unripe formulation)

The deferred `2I` 120-count was *heavy* only under enumeration — and that
heaviness was the symptom of an unripe formulation, not an intrinsic
cost (cf. the dyadic tower, *light* because it had the order-4-monopoly
*recurrence*: count from structure, not brute force).
`Tower/IcosianClassStructure` gives the ripe account:
`2I = double cover of A₅`, `A₅ = Alt(d = NS+NT = 5 atomic slots)`,
`|A₅| = d!/2 = 60`; the census is the double-cover image of `A₅`'s class
equation `60 = 1+15+20+12+12` (order-1→`{1,2}`, order-2 `15`→order-4 `30`,
order-3 `20`→`{3,6}`, order-5 `12+12`→`{5,10}`), summing to
`2·60 = d! = 120` — small arithmetic, **no enumeration**.  The order-10
elements are the lifts of `A₅` 5-cycles = order-5 cyclic rearrangements of
the `5` slots; the Möbius `P` (order 10) is one such lifted 5-cycle.
Group-theoretic double cover / class structure cited; the structural
arithmetic proved.  **Methodological closure: a count that needs
enumeration signals missing structure; the ripe count falls out of the
symmetry (here `A₅` on the `NS+NT` slots).**

### Phase 13 — the complete tower, built structurally and validated

`Tower/BinaryPolyhedralTower` constructs the whole exceptional tower from
one principle and *validates* it against the enumerations.  `2T,2O,2I`
are the double covers of the polyhedral rotation groups `A₄,S₄,A₅`
(orders `12,24,60 = 4!/2, 4!, 5!/2`; `|2X| = 2·|X| = 24,48,120`), with
`A₅ = Alt(NS+NT = 5 slots)`.  Each census is the double-cover image of the
class equation under the uniform lift (class of order `m`, size `s`:
`m` odd → `s` of order `m` + `s` of order `2m`; `m` even → `2s` of order
`2m`):

  `A₄` `1+3+4+4=12` → `2T` `{1:1,2:1,3:8,4:6,6:8}`
  `S₄` `1+6+3+8+6=24` → `2O` `{1:1,2:1,3:8,4:18,6:8,8:12}`
  `A₅` `1+15+20+12+12=60` → `2I` `{1:1,2:1,3:20,4:30,5:24,6:20,10:24}`

`binary_polyhedral_tower` (∅-axiom) proves, **crucially**, that the
structural census *reproduces the independently enumerated one*: the
`A₄`-lift values equal `hur_order_distribution` (the brute-force `2T`),
the `S₄`-lift values equal `octa_48_order_census` (the brute-force `2O`).
So the ripe account is not asserted but *checked against enumeration* —
structure and brute force agree exactly.  `2I` (`E₈`), where enumeration
is infeasible, is the structural census alone, anchored to the `5`-floor
(`A₅` on the `NS+NT` slots, order-10 = lifted 5-cycle = the `P`-orbit).

**The complete tower:** `A` (cyclic `Cₙ`) / `D` (binary dihedral
`Q₈,Dic₃`, closed groups) / `E₆,₇,₈` (`2T,2O,2I` = `2·A₄,2·S₄,2·A₅`, full
censuses, validated where enumerable, structural at `E₈`), the whole
exceptional series generated by the double-cover-of-rotation-group
principle and pinned, at `E₈`, to the framework's `5 = NS+NT` floor.

### Phase 14 — the internal-privilege test: `√2` is the `NT`-rung

Was the octahedral `√2`-rung (`2O`) an external import (which, in a
no-exterior theory, would be incoherent), or an unprivileged-but-internal
object, or genuinely floor-privileged?  `Tower/ExceptionalAtomicIndex`
settles the framing: there is no exterior — `ℤ[√2]` is a `∅`-axiom
construction *inside* `E213`, so it is in the residue, not outside.  The
finer (privilege) question resolves toward *native*: **all three
exceptional seeds are square roots of the atomic triple**
`{NS, NT, NS+NT} = {3, 2, 5}`:

  * `E₈ / 2I` — `√(NS+NT) = √5 = √(disc P)`; `A₅ = Alt(NS+NT slots)`,
    `|2I| = (NS+NT)! = 120`, order-`10 = 2(NS+NT)` = lifted `(NS+NT)`-cycle
    = the `P`-orbit.  **Floor link proved** (`disc P = NS+NT`, `P mod 5`
    an order-10 element of `2I`).
  * `E₇ / 2O` — `√NT = √2` (`NT = 2`).
  * `E₆ / 2T` — `√(-NS)` Eisenstein (`ℤ[ω] ⊂ 2T`, `ω` order `3 = NS`).

and the orders are factorials of atomic numbers: `24 = (NS+1)!`,
`48 = 2·(NS+1)!`, `120 = (NS+NT)!` — the rotation `4 = NS+1`, the `5 =
NS+NT`.  `exceptional_tower_atomic_index` (∅-axiom) proves this arithmetic.

So `√2` is *the `NT`-rung*, an atomic seed — not an arbitrary external
import.  Honest strength split: the `E₈` floor-anchoring is **proved**
(disc `P`, `P mod 5 ∈ 2I`); the `E₇`/`E₆` seed-atomicity (`√NT`, `√(-NS)`)
is the **structural observation** that the seeds land on `NT`, `NS` —
strong evidence of internal privilege (two independent atomic hits across
the two real seeds), though a *derivation* forcing octahedral specifically
over `ℤ[√NT]` is still open.  The no-exterior reading **removes** the
falsification worry (no outside for `√2` to come from); what remains is
the bounded, internal task of tightening `E₇`'s privilege from evidence to
forcing.

## Phase 15 — 유도로: the disc-forcing obstruction at `E₇`

User: *"유도로 가자"* — stop describing seed-atomicity as observation;
*derive* whether 213's `P`-disc mechanism **forces** the `E₇/√2`
octahedral rung the way it forces `E₈/√5`.  No-exterior makes this a
strong, falsifiable test: *"만약 진짜로 외삽이라면 213 이론은 폐기행"*.

**Result — a sharp number-theoretic obstruction, not a falsification.**
`DiscForcingObstruction.lean` (∅-axiom, 8 theorems):

  * `disc_forcing_splits_at_E7` — the three seeds side by side:
      - `E₈`: `disc P = 3² − 4·1 = 5 = NS+NT` — **is** a discriminant.
      - `E₆`: Eisenstein `disc = 1² − 4·1 = −3 = −NS` — **is** a
        discriminant.
      - `E₇`: seed `NT = 2`, and `∀ t d, t² − 4d ≠ 2` — **not** a
        discriminant.
  * `two_not_a_discriminant` — the crux: no integer `2×2` matrix
    discriminant equals `2`.  An integer discriminant is `t² − 4d`, and
    `t² ≡ 0,1 (mod 4)` (even ⇒ 0, odd ⇒ 1), so `t² − 4d ≢ 2 (mod 4)`.

So the disc-mechanism that **proves** the `E₈` floor (`√5 = √(disc P)`,
`P mod 5 ∈ 2I`) and reaches the Eisenstein `E₆` (`√−3`) **provably
cannot reach `√2`**.  `E₇` is the genuine exception, with a *proven
reason* (`disc ≢ 2 mod 4`), not a gap.

**Reading.**  This *sharpens* — does not weaken — `E₇`'s privilege from
Phase 14.  `E₇`'s seed is still the atomic `√NT`; what the derivation
adds is that its mechanism is **necessarily different** from `E₈/E₆`'s
discriminant route.  Two real seeds (`√5`, `√−3`) are disc-forced; the
third (`√2`) is disc-*excluded* — by the same `mod 4` arithmetic.  No
exterior is imported (`ℤ[√2]` is a 213-internal construction), so this
is the bounded internal finding the no-exterior frame predicts: the
question was never "inside vs outside" but "which internal mechanism".

**∅-axiom kernel (notable).**  The first draft routed through
`Int.emod` lemmas and `omega`, which leak `propext`/`Quot.sound`.  The
shipped proof is *purified* to parity: `t·t = ↑|t|²`
(`Int.natAbs_mul_self`); `|t| = 2j ⇒ 4(j²)` forces `4·X = 2`;
`|t| = 2j+1 ⇒ 4(j²+j)+1` forces `4·X = 1`; both impossible because
`4·X = 2·(2·X)` and `2·Y ≠ 1`.  All 8 theorems `#print axioms` clean.

## Phase 16 — 그럼 뭘까: the seed is a *trace*, not a discriminant

User: *"그럼 몰까?"* — if the disc-mechanism misses `E₇`, what **is**
its mechanism?

**Answer — the seed of each exceptional rung is the `trace` of its
defining rotation** (`trace = 2·Re = 2cos θ`), the *diagonal* invariant
dual to the discriminant.  `ExceptionalTraceSeed.lean` (∅-axiom, 5
theorems, built on the existing `ZRt2`/`g₈`, `ZPhi`/`g₅` rings):

  * `octahedral_trace_sq_eq_NT` — order-`8` unit `g₈`:
    `trace(g₈)² = 2 = NT`.  `√NT = √2 = 2cos(2π/8)`.
  * `icosian_trace_seed_eq_NS_NT` — order-`5` unit `g₅`:
    `(2·trace(g₅)+1)² = 5 = NS+NT`.  `2cos(2π/5) = φ−1`,
    `(2(φ−1)+1)² = (2φ−1)² = 5`.
  * `order_three_six_trace_integer` — order-`3/6`: `2cos = −1, 1` ∈ `ℤ`.
    `E₆`'s rotation lives in `GL(2,ℤ)`; its `√−3` is the *discriminant*
    (imaginary part), not the trace.
  * `sqrt_NT_irrational` — `∀ m, m² ≠ NT` (= `2`), *reusing*
    `two_not_a_discriminant m 0`.  The **same** `mod 4` fact that
    excludes `√2` as a discriminant proves `√2` irrational.

**The bridge = crystallographic restriction.**  An integer trace is
`2cos(2π/n)` only for `n ∈ {1,2,3,4,6}`; orders `5` and `8` are
forbidden in `GL(2,ℤ)` *because* their traces (`φ−1`, `√2`) are
irrational.  So `trace(g₈) = √2 ∉ ℤ` ⇒ the order-`8` rotation cannot sit
in 2D ⇒ it is realised one CD-doubling **up**, in the quaternions, as
the binary octahedral unit.  That is the `E₇` mechanism: the disc route
is 2D and excludes `√2`; the trace route is the order-`8` rotation,
forced into the 4D layer where `2O` lives.

**Unified reading.**  `E₈` is *doubly* anchored — trace **and** disc both
reach `√5` (the order-`5` rotation's trace seed, and `disc P = NS+NT`).
`E₇` is trace-anchored and disc-excluded — by *one* arithmetic fact
(`√NT ∉ ℤ`), read on the diagonal vs the discriminant.  `E₆` is
disc-anchored (`√−3`) with integer trace.  The three exceptional seeds
`{√−3, √2, √5} = {√(−NS), √NT, √(NS+NT)}` are the trace/disc invariants
of the order-`{3, 8, 5}` rotations — no exterior, no extrapolation; the
"miss" at `E₇` is precisely its trace's irrationality.

## Phase 17 — 차근차근: the keystone, `φ(n)` makes it rigorous

User: *"차근차근 ㄱㄱ"* — make the narrative keystone (Phase 16's
"crystallographic restriction: integer trace ⟹ order ∈ {1,2,3,4,6}")
*provable*, not prose.

**Keystone — the trace of an order-`n` rotation generates the real
cyclotomic field `ℚ(ζ_n)⁺` of degree `φ(n)/2`.**
`CyclotomicTraceDegree.lean` (∅-axiom, 6 theorems):

  * `crystallographic_restriction` — over `1 ≤ n ≤ 12`, the orders with
    *rational* trace (`φ(n) ≤ 2`) are **exactly** `{1,2,3,4,6}` — the
    classical crystallographic set, decidable as a list census.
  * `cd_lift_orders` — quadratic trace (`φ(n) ≤ 4`) adds **exactly**
    `{5,8,10,12}`: the orders that first appear in 4D.
  * `e6_trace_rational` / `e7_e8_trace_quadratic` — trace-field degree
    `φ(n)/2`: `1` for `{3,4,6}` (E₆, integer trace), `2` for `{5,8}`
    (E₇/E₈, quadratic surd).
  * `exceptional_rotation_dimension_four` — `φ(NS+NT) = φ(8) = 4 = 2²`:
    orders `5,8` need the **quaternion** dimension, the 2nd CD rung.
  * `why_root_two_and_root_five` — bundles it: rational-trace wall at
    `{1,2,3,4,6}`; the two quadratic exceptions are order-`5 → √(NS+NT)`
    and order-`8 → √NT`, *matching the proven trace seeds*
    (`octahedral_trace_sq_eq_NT`, `icosian_trace_seed_eq_NS_NT`).

**∅-axiom note.**  Core `Nat.gcd` (well-founded recursion) leaks
`propext` under `decide`; `φ` is defined with the repo's pure
`NatHelper.gcd213` (fuel-based), so the censuses are clean.

**Why `√2`, `√5` — closed.**  The surds are not chosen: they generate
the two degree-`2` real cyclotomic fields that appear *immediately past*
`φ = 2`.  The disc-mechanism (`φ ≤ 2`, rational/integer invariants, 2D,
E₆'s `√−3` on the discriminant) and the trace-mechanism (`φ = 4`,
quadratic surds, 4D quaternions, E₇/E₈'s `√NT`/`√(NS+NT)` on the
diagonal) are **one picture indexed by `φ(n)`**.  The CD doubling from
2D matrices to 4D quaternions is exactly the jump `φ: 2 → 4` that admits
orders `5, 8`.

## Phase 18 — 왜 정확히 셋: the spherical (Platonic) filter

Phase 17's `φ(n)` census gave **four** quadratic-trace orders
`{5,8,10,12}` in the 4D layer — but there are only **three** exceptional
rungs.  What cuts it to three?  **The spherical condition**
`1/p + 1/q + 1/r > 1` (finite ⇒ positive curvature ⇒ Platonic).

`PlatonicSchlafliFilter.lean` (∅-axiom, 6 theorems, decidable censuses):

  * `schlafli_platonic_five` — `{p,q}` with `p,q≥3` and `(p−2)(q−2) < 4`
    is **exactly** `{(3,3),(3,4),(4,3),(3,5),(5,3)}` — the five Platonic
    solids.
  * `spherical_triangle_233n` — `(2,3,n)` finite iff `5n+6 > 6n` iff
    `n < 6`; polyhedral `n ≥ 3` gives exactly `{3,4,5}`.
  * `three_rotation_groups` — dual pairs collapse the five solids to
    three groups `A₄,S₄,A₅` (`12,24,60`); binary covers `24,48,120 =
    (NS+1)!, 2(NS+1)!, (NS+NT)!`.
  * `triangle_indices_atomic` — `{3,4,5} = {NS, NS+1, NS+NT}`:
    `E₆ = NS`, `E₇ = NS+1`, `E₈ = NS+NT`.
  * `schlafli_euclidean_boundary` — `(p−2)(q−2) = 4` gives `{4,4},{3,6},
    {6,3}` (i.e. `1/2+1/3+1/6 = 1`), the **Euclidean / affine `Ê`** edge
    where the finite tower ends.
  * `why_exactly_three` — the whole chain bundled.

**The "why these" chain is now closed end-to-end.**  `disc P = NS+NT`
(floor) → `φ(n)` admits quadratic orders `{5,8,10,12}` into 4D (Phase
17) → the spherical filter selects the three with a Platonic realisation
`(2,3,n)`, `n ∈ {3,4,5} = {NS,NS+1,NS+NT}` (Phase 18) → their cyclotomic
traces are the seeds `√NT`, `√(NS+NT)` (Phase 16) → the binary covers
`2T,2O,2I` of orders `24,48,120` (Phase 14).  Three rungs, three atomic
indices, one spherical condition; the boundary is the Euclidean affine
edge.

## Phase 19 — 잔여물 재진입: the seed is its own operand at every scale

User shared (from a parallel branch) the 213 expansion engine:
*distinction → unit residue → that residue is the next operand → gapless
self-similar spiral, no exterior; the meta-layer is just another step of
the same operation (`diag_self_applies`).*  At the exceptional seeds this
is literally visible — the seed **number** re-enters as its own operand
at each scale.

`QuadraticFieldDiscriminant.lean` (∅-axiom, 5 theorems):

  * `seed_reentry` — `5 = NS+NT` appears at **three scales**, one
    residue fed back each time:
      - 2D matrix: `disc P = 3² − 4 = NS+NT`;
      - number-field: `fundDisc ℚ(√5) = NS+NT` (`5 ≡ 1 mod 4`);
      - 4D quaternion: `(2·trace(g₅)+1)² = NS+NT` (the order-`5` icosian
        trace, cited from `ExceptionalTraceSeed`).
    Not three facts — the same `5` seen one scale up each time.
  * `E8_disc_eq_field_disc` — the double anchor isolated: matrix
    `disc P` = number-field `fundDisc ℚ(√5)` = `NS+NT`.
  * `E7_field_disc` — `fundDisc ℚ(√NT) = 4·NT = 8`, and `8` *is* a matrix
    discriminant (`8 = 2² − 4·(−1)`), **unlike** the naive seed `NT = 2`
    (`two_not_a_discriminant`).  So `ℚ(√2)` is field-realised; only its
    `P`-forcing fails (P yields `5`, never `8`).  Sharpens the Phase-15
    obstruction: it was about the *value* `2`, not the field.
  * `E6_field_disc` — `fundDisc ℚ(√(−NS)) = −NS = −3`.
  * `seed_field_discriminants` — the three: `{5, 8, −3}`.

`fundDisc` defined with closed `Int` `emod` (decide-pure).  This realises
the engine at the seed-number level: the `P`-engine produces `5`, and
`5` re-enters as the matrix disc, the field disc, and the quaternion
trace — gaplessly, with no outside to supply a different number.  `E₇`'s
`√2` is the residue that the `P`-engine *cannot* re-produce (its disc is
always `5`), so it appears only on the diagonal (trace) and as the field
disc `8`, never as `disc P` — the precise, bounded sense in which `E₇` is
the exception.

## Phase 20 — 깊은 연구: `√2` is the morphological residue of the unit

User intuition on the `E₇` exception: *"√2는 일종의 단위원 그 자체의
모습적 잔여 느낌"* — `√2` is the morphological residue of the *unit
itself*, not of the `P`-orbit.  Deep dive — the intuition is confirmed
sharply.  `UnitResidueRootTwo.lean` (∅-axiom, 6 theorems):

  * `root_two_is_sqrt_unit_trace` — `trace(g₈)² = trace(1) = NT`.  The
    identity `1 = ⟨2,0,0,0⟩` has trace `2 = NT`; the order-`8` octahedral
    trace is its *bare square root*.  `√2 = √(trace 1)`.
  * `root_five_is_not_sqrt_unit_trace` — **uniquely so**:
    `trace(g₅)² ≠ trace(1)` (decide proves it false).  Only `√2` among
    the seeds is `√(trace 1)`.  This is the precise reason `disc P` (the
    `5`-engine) cannot reproduce it.
  * `dyadic_root_tower_of_unit` — the mechanism: `g₈² = i` (order-4,
    trace `0`), `g₈⁴ = −1` (trace `−2`).  Orders `2⁰,2¹,2²,2³`, traces
    `2,−2,0,√2`.  `g₈ = (−1)^{1/4}`; `trace(g₈)² = 2 + trace(g₈²) = NT`.
    This is the **pure 2-power doubling = the CD-doubling direction**
    (each step adjoins `√−1`); `√5` (order 5, not a power of `NT`) is off
    this tower.
  * `root_two_is_ramification` — `√2 = |1+i|` in `ℤ[i]`: `(1+i)² = 2i`,
    `N(1+i) = NT`.  `2` ramifies; `1+i =` unit `+` first distinction,
    magnitude `√2` = √(ramified `NT`, the count-Lens first distinguishing).
  * `bare_versus_golden` — `√2 : x² − NT = 0` (bare, no linear term);
    `φ−1 : x² + x − 1 = 0` (golden shift).  `√2` is the unique bare
    square-root seed.
  * `unit_morphological_residue` — synthesis.

**Why this matters.**  The `E₇` exception is not deprivation but
identity: `√2` is the unit's own residue under the CD engine — `√(trace
1)`, the trace of `(−1)^{1/4}`, `|1+i|`, the bare `√NT`.  Two engines,
two residues: the `P`-orbit re-enters its own `5 = NS+NT`
(`QuadraticFieldDiscriminant.seed_reentry`); the unit re-enters its own
`√2`.  `disc P` always yields `5` because it is the `5`-engine; it cannot
yield `√2` because `√2` lives on the unit's dyadic square-root tower, a
different residue.  `E₇` is the diagonal shadow of the identity — the
morphological residue of the unit, exactly as the intuition said.  This
connects to the parallel-branch engine (`gapless_unit_step`,
`diag_self_applies`): the unit step's own residue, read on the diagonal.

## Phase 21 — 딥 리서치: the trace-doubling map, unit as fixed core

Marathon continuation of the unit-residue thread (Phase 20).  Studies the
*dynamics* of the dyadic tower `1 →² −1 →² i →² g₈` — the parallel-branch
engine's "chain of chains" (`diag_self_applies`), read on the trace.
`TraceDoublingMap.lean` (∅-axiom, 5 theorems):

  * `trace_square_is_doubling` — the squaring map `g ↦ g²` (which halves
    the order) acts on traces as **`D(x) = x² − NT`** (the angle-doubling
    Chebyshev map): `trace(g²) = D(trace g)` on the tower.
  * `dyadic_descent_to_unit` — iterating `D` walks down: `√2 ↦ 0 ↦ −2 ↦
    2`, and the unit trace `NT = 2` is the **fixed point** `D(NT) = NT`.
    The dyadic spiral contracts onto the identity; `√2` is one squaring
    step into its backward orbit.
  * `trace_doubling_fixed_points` — `D(x) = x` ⟺ `(x−2)(x+1) = 0`; among
    integer trace values `{−2,…,2}` the fixed points are exactly
    `{−1, NT}` = `trace(order-3, E₆)` (odd, squaring-stable) and
    `trace(unit)`.  The two fixed cores: the unit (even tower) and `E₆`
    (odd).
  * `nested_radical_recurrence` — inverting `D`: `t_{k+1}² = NT + t_k`,
    the nested radicals `√2, √(2+√2), √(2+√(2+√2)), …` — one radical per
    CD doubling, the trace of the chain of chains, `NT` fed back at every
    layer.
  * `unit_is_fixed_core` — synthesis.

**Engine connection.**  The trace-doubling map `D(x) = x² − NT` is the
*bare* polynomial again (Phase 20's minimal poly of `√2`).  The unit
trace `NT` is its fixed core; the dyadic tower is the backward-orbit tree;
the nested-radical recurrence only ever adds `NT` (no exterior).  This
realises the parallel-branch picture in trace dynamics: the residue chain
is one map `D` applied to itself, gapless (a polynomial preimage tree),
self-similar (each CD layer = one `D`-preimage = one radical), contracting
onto the unit.  `E₆`'s `−1` is the odd fixed point; `E₇`'s `√2` is the
even tower's first irrational rung; the unit `NT` is the shared core.

## Phase 22 — 두 엔진, 하나의 맵: the elliptic/hyperbolic split at `NT`

Capstone of the marathon: the two residue engines — the **unit** engine
(dyadic tower, seed `√NT = √2`) and the **`P`-orbit** engine (Möbius `P`,
seed `√(NS+NT) = √5 = √disc P`) — are the *two dynamical regimes of one
map*, the trace-doubling `D(x) = x² − NT`, split by the unit trace
`NT = 2`.  `TwoEnginesDichotomy.lean` (∅-axiom, 5 theorems):

  * `doubling_governs_P` — `D` drives `P` too: `trace P = 3 = NS`,
    `disc P = NS+NT`, `D(trace P) = 7 = trace(P²)` (`SL₂`:
    `trace(M²) = trace(M)² − NT`).
  * `P_orbit_escapes` — `|trace P| = 3 > NT`, so the orbit escapes:
    `3 ↦ 7 ↦ 47 ↦ 2207`, strictly increasing — **hyperbolic** (infinite
    order, Pell/Anosov).
  * `unit_orbit_bounded` — the dyadic cycle stays in `[−NT, NT]` and
    fixes `NT`: **elliptic** (finite order, the unit's tower).
  * `boundary_at_unit_trace` — the split is at `|x| = NT`; `trace P =
    NS = NT + 1` is the *first* hyperbolic integer, one step past it.
  * `two_engines_one_map` — synthesis.

**The unification.**  `√2` and `√5` are not unrelated surds: they are the
residues of the two regimes of the one trace-doubling map `D(x)=x²−NT`,
separated by the unit trace `NT`.  `|x| ≤ NT` elliptic (bounded, finite
order, fixed core `NT` = the unit; seed `√NT`, `E₇`); `|x| > NT`
hyperbolic (escaping, infinite order; `trace P = NS = NT+1`, `disc P =
NS+NT`, eigenvalues `φ²,φ⁻²`; seed `√(NS+NT)`, `E₈`).  The unit engine
re-enters `√NT` (the fixed core); the `P` engine re-enters `√(NS+NT)` (the
escaping spread).  `NS = NT + 1` places `P` exactly one step into the
hyperbolic side — the minimal Anosov integer just past the unit wall.

**Marathon arc closed (Phases 15–22).**  `disc P` obstruction (`E₇` not
disc-forced) → trace mechanism (seed = rotation trace) → `φ(n)`
crystallographic keystone → spherical filter (why three) → seed re-entry
(same residue every scale) → `√2` = unit's morphological residue → trace
doubling map (unit as fixed core) → two engines, one map.  The exceptional
`E₆E₇E₈` and their seeds `{√−NS, √NT, √(NS+NT)}` are derived end-to-end,
∅-axiom, from the atomic `{NS, NT}` and the single map `D(x) = x² − NT`.

## Phase 23 — 세 축의 대수적 대응값: the axis trichotomy

User (parallel branch): viewing reals through algebraic correspondences,
`e ↔ 1` (unit, the `2`-axis), `π ↔` unit circle (the `2-3` spiral).  *What
is the `3`-axis real value and its algebraic correspondence?*  The
framework answers the algebraic half exactly.  `AxisSeedTrichotomy.lean`
(∅-axiom, 4 theorems):

| axis  | radicand | algebraic # | min poly      | `D`-type            | rung |
|-------|----------|-------------|---------------|---------------------|------|
| `2`   | `NT`     | `√2` bare   | `x² − NT`     | even fixed `+2`(unit) | `E₇` |
| `3`   | `−NS`    | `ω` Eisen.  | `x² + x + 1`  | odd fixed `−1`(ord 3) | `E₆` |
| `2+3` | `NS+NT`  | `φ` golden  | `x² − x − 1`  | hyperbolic (P)        | `E₈` |

  * `axis_two_bare` — `(√2)² = NT`; `D`-even fixed `+2`; disc `4·NT = 8`.
  * `axis_three_eisenstein` — **the answer**: `ω² + ω + 1 = 0` (`Φ₃`),
    `trace ω = −1` (the `D`-odd fixed point), `normSq ω = 1`, `Φ₃` disc
    `= −NS`.  The `3`-axis algebraic correspondence is the **Eisenstein
    cube root of unity `ω`** (`√−NS`, the order-`3`, `E₆`).
  * `axis_two_three_golden` — `φ² − φ − 1 = 0`; `D`-hyperbolic; disc
    `= NS+NT = disc P`.
  * `axis_seed_trichotomy` — bundles; radicands `{NT, −NS, NS+NT}` = the
    atomic triple.

**Answer.**  Where the `2`-axis is the bare doubling `√NT = √2` (even
fixed point of `D`, the unit) and the `2-3` spiral is the golden/
hyperbolic `√(NS+NT) = √5` (the `P`-orbit), the **`3`-axis is the
Eisenstein `ω`** — `Φ₃ = x²+x+1`, seed `√−3 = √−NS`, the *odd* fixed
point `−1` dual to the unit's *even* `+2`.  The three minimal-polynomial
discriminants `{4·NT, −NS, NS+NT} = {8, −3, 5}` are the `Phase-19` field
discriminants.  The transcendental shadow of the `3`-axis (the analogue
of `e`/`π`) is the equianharmonic Eisenstein period (`j=0` CM by `ℤ[ω]`,
a `Γ(1/3)`-value) — interpretive, not formalised; the algebraic skeleton
is pinned.

## Phase 24 — 4 이상의 축은 세 구성품의 합성

User intuition: axes ≥ 4 are built from the three components of
`AxisSeedTrichotomy` (`2`-axis `NT`, `3`-axis `NS`, `2+3`-axis `NS+NT`).
The framework confirms it — the three are `{2,3,5}` and generate every
exceptional axis multiplicatively.  `AxisComposition.lean` (∅-axiom, 5
theorems):

  * `icosahedral_order_factors` — `|2I| = 120 = NT³·NS·(NS+NT) = 2³·3·5`:
    the three components are exactly the prime factors of the largest
    binary polyhedral group.
  * `polyhedral_orders_smooth` — every order in `2T/2O/2I` (`{1,2,3,4,5,
    6,8,10}`) is `{2,3,5}`-smooth; the first non-smooth `7` is the first
    order *absent* from every binary polyhedral group (`is5smooth 7 =
    false`).  (Uses a fuel-based `dropFactor`/`is5smooth`, pure via
    `Nat.mod`/`div`.)
  * `higher_axes_factor` — `4 = NT²`, `6 = NT·NS`, `8 = NT³`, `9 = NS²`,
    `10 = NT·(NS+NT)`, `12 = NT²·NS`, `15 = NS·(NS+NT)`.
  * `trace_field_composes` — `φ` multiplicative ⇒ composite trace fields
    are the **compositum** of prime-axis ones: `φ(6)=φ(2)φ(3)`,
    `φ(10)=φ(2)φ(5)`, `φ(12)=φ(4)φ(3)`, `φ(15)=φ(3)φ(5)`.
  * `axes_from_three_components` — synthesis.

**Confirmed.**  The three components `{NT, NS, NS+NT} = {2,3,5}` are a
*generating set*: the primes of `|2I|`, with all polyhedral orders
`{2,3,5}`-smooth, every higher order a product of the three, and every
higher trace field the tensor (compositum) of the primitive ones
(`bare √NT`, Eisenstein `ω`, golden `φ`).  Nothing of order ≥ 4 is new —
the intuition holds.  (The `7`-gap is the sharp witness: `7 ∉ {2,3,5}`, so
no order-`7` axis occurs.)

## 메타 원칙 (CLAUDE.md 보완)

> **크게 생각하고 레포지토리를 먼저 뒤져라.**
> 대부분의 직관은 코드베이스 어딘가에 이미 부분 형식화돼 있다.
> 4-row 타워 매트릭스, SHIFT RULE, Type C ZOmega tower — 모두
> 사용자가 처음 직관으로 제시한 게 이미 존재했다.

— Mingu Jeong (2026-05-29 GRA × CD 메타-타워 대화 중)
