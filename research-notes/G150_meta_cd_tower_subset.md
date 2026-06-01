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

## 메타 원칙 (CLAUDE.md 보완)

> **크게 생각하고 레포지토리를 먼저 뒤져라.**
> 대부분의 직관은 코드베이스 어딘가에 이미 부분 형식화돼 있다.
> 4-row 타워 매트릭스, SHIFT RULE, Type C ZOmega tower — 모두
> 사용자가 처음 직관으로 제시한 게 이미 존재했다.

— Mingu Jeong (2026-05-29 GRA × CD 메타-타워 대화 중)
