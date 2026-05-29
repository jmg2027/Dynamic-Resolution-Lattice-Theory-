# Session handoff

Branch: `claude/gra-promotion-essay-LwwoA` — GRA Phases 1–22 closed
(all PURE / 0 DIRTY post-consolidation).  Plus: `theory/THEORY_BOOK.md`
v1.2 + duplication-cleanup passes.

## G150 Marathon — meta-CD-tower typeclass migration (Phases 1-3 + Phase 4 Type A/B/C bases closed)

Architecture path: classical CD tower (Type A: Lipschitz → Cayley →
Sedenion → ...) is one *column* of a 4-row matrix (Types A/B/C/D ×
CD doubling layer) already partially formalised in the repo
(`theory/math/cayley_dickson/algebra_tower.md` §"4-row matrix",
`Integer/{ZI,ZOmega,ZSqrt,Hurwitz213}`, SHIFT RULE in
`ZSqrtMinus2Findings`).  Migration goal: lift `hurwitz_ring`-based
DIRTY proofs to PURE typeclass projections via `MoufangIntegerNormed213`
(commit `ff76af2`).

  · **Phase 1** (commit `e0da617`): ZOmega CommStarRing213 +
    IntegerNormed213 — Type C base instance.  Generic `normSq_mul`
    via typeclass replaces `ZOmegaDomain` `quad_norm` proof.  Purity
    `[propext, Quot.sound]` → `[propext]` only (Quot.sound removed).
    New file `ZOmegaAlgebra213.lean` (305 lines), mirror of
    `ZIAlgebra213` with ω² = -1 - ω cross-term.  Add/Neg/Sub
    relocated to ZOmega.lean (foundational).
  · **Phase 2** (commits `38e17ad`, `620ab3c`): ZOmegaDouble
    Ring213 + StarRing213 via abstract `CDDouble ZOmega` bridge.
    Concrete struct iso to abstract type (rfl on mul/conj/add/neg/
    zero).  All 7 Ring213 + 4 StarRing213 axioms via 3-line bridge
    proofs.  NO 32-Int-var polynomial proof at this layer.
  · **Phase 3** (commit `0d6d9e8`): ZOmegaDouble IntegerNormed213
    + ZOmegaQuad bridge skeleton.  The actual completion of Type C
    base layer migration.  Generic `IntegerNormed213.normSq_mul`
    derives ZOmegaDouble's norm multiplicativity via typeclass
    projection — replaces `quad_norm`-based DIRTY proof.  All 5
    IntegerNormed213 fields hand-proven (ofInt_inj', ofInt_add',
    ofInt_mul', ofInt_central', self_mul_conj').  ZOmegaQuad
    Add/Neg/Sub relocated foundationally.

Validates the parametric Algebra213 path completely at Type C base
layer: ZOmega → CommStarRing213 → abstract CDDouble ZOmega →
Ring213 + StarRing213 (auto-synthesis) → ZOmegaDouble via bridge →
IntegerNormed213 ZOmegaDouble → generic normSq_mul = typeclass
projection.  Removes `hurwitz_ring` / `quad_norm` polynomial
expansion from Type C base layer entirely.

  · **Phase 4 foundation** (commit `7d5dafa`): ZOmegaDouble
    `normSq_conj` (via CommRing213.mul_comm + ofInt_inj — no
    polynomial expansion) + `conj_mul_self` (reverse self_mul_conj).
    Both `[propext]`-only.
  · **Phase 4 ZOmegaDouble Moufang** (commit `0274ab3`):
    AlternativeNormed parametric bridges
    (`[Ring213 α] → NonAssocRing213 α` +
    `[StarRing213 α] → NonAssocStarRing213 α`) +
    `instance : MoufangIntegerNormed213 ZOmegaDouble` registered.
    Moufang norm-collapse trivially from `mul_assoc` (associative
    quaternion-analog layer).  Witness `moufang_normSq_mul`
    `[propext]`-only.
  · **Phase 4 Lipschitz Moufang** (commit `8cfa7aa`): Type A
    counterpart.  `LipschitzMoufang.lean` (61 lines) registers
    `instance : MoufangIntegerNormed213 Lipschitz` with same
    recipe (mul_assoc trivializes Moufang at associative layer).
    `moufang_normSq_mul` verified **strict ∅-axiom** (does not
    depend on any axioms) — stronger than ZOmegaDouble path
    because ZI uses simpler ring-axiom proofs (no neg_add in
    simp set).
  · **Phase 4 ZOmega normSq_mul DIRTY removal** (commit `edbcb53`):
    architectural cycle break (mul_comm relocated to ZOmega.lean
    foundationally) enables ZOmegaDomain.normSq_mul to use
    `IntegerNormed213.normSq_mul` typeclass projection directly.
    Replaces `quad_norm` body in production:
      was: `[propext, Quot.sound]` (simp + omega)
      now: `[propext]` only           (typeclass)
    Quot.sound eliminated from the call-site theorem.  Real
    architectural win — typeclass framework REPLACES DIRTY tactic
    in production code, not just provides an alternative.

Validates MoufangIntegerNormed213 at both Type A L2 (Lipschitz,
PURE) and Type C L3 (ZOmegaDouble, [propext]) — the associative
quaternion-analog layers in both base towers.

  · **Phase 4+ Type B base** (commits `8f8138c`, `65b7244`):
    ZSqrt[D] parametric in D registered as CommStarRing213 +
    IntegerNormed213.  Full hierarchy Ring213 → CommRing213 →
    StarRing213 → IntegerNormed213 → CommStarRing213.
    Cross-tower framework now active at all 3 base towers
    (Type A ZI/Lipschitz, Type B ZSqrt[D], Type C ZOmega/
    ZOmegaDouble).  Concrete ZSqrt2, ZSqrtMinus2 inherit via D
    specialization.  `[propext]`-only.
  · **Phase 4+ Type B downstream** (commits `8669bf3`, `6820e60`,
    `8df00cc`): L3T (= CDDouble ZSqrt 2, Type B L3 carrier from
    ZSqrtMinus2Tower) registered as Ring213 + StarRing213 via
    abstract bridge (toCDDouble), then IntegerNormed213 via direct
    field proofs.  Generic `IntegerNormed213.normSq_mul` derives
    L3T's norm-multiplicativity via typeclass projection.
    `[propext]`-only.  L4T = CDDouble L3T is the alternative
    non-assoc layer (Cayley analog), requires Phase 4 capstone work.
  · **Phase 4+ cross-tower Moufang at all 6 framework instances**
    (commits `e4c43fe`, `f077ab0`): MoufangIntegerNormed213 instance
    registrations.  Trivial Moufang via mul_assoc at every
    associative layer:
      - 3 commutative bases: ZI (strict ∅-axiom), ZSqrt[D]
        ([propext], parametric), ZOmega ([propext])
      - 3 L2/L3 quaternion-analogs: Lipschitz (strict ∅-axiom),
        ZOmegaDouble ([propext]), L3T ([propext])
    Generic MoufangIntegerNormed213.normSq_mul (7-step calc-chain)
    derives Hurwitz norm-multiplicativity at all six.  ZSqrt[D]
    auto-derives for any D specialization (ZSqrt 2, ZSqrt -2,
    ZSqrt 3, ...).
  · **Phase 4+ non-assoc parametric instances on CDDouble** (commit
    `97d04d9`): weaken `conj_mul'` in `CDDoubleStar.lean` from
    `[CommStarRing213 α]` to `[StarRing213 α]` (proof needs only
    additive comm + neg_add/neg_mul + base anti-distrib conj_mul; no
    multiplicative comm).  Add parametric instances:
      · `instNonAssocRing213CDDoubleStar    [StarRing213 α]`
      · `instNonAssocStarRing213CDDoubleStar [StarRing213 α]`
    These fire on any non-commutative associative *-ring base,
    unlocking the Cayley-analog layer typeclass status throughout.
  · **Phase 4+ ZOmegaQuad NonAssocStarRing213** (commit `97d04d9`):
    Type C L4 (24 units, M_24 Chein loop) registers as
    NonAssocRing213 + NonAssocStarRing213 via toCDDouble bridge.
    [propext]-only purity.
  · **Phase 4+ L4T + Cayley NonAssocStarRing213** (commit `75333f2`):
    completes the alt-layer cross-tower coverage:
      - Type A L3 Cayley = CDDouble Lipschitz  (strict ∅-axiom!)
      - Type B L4 L4T    = CDDouble L3T        ([propext])
    All 3 alternative non-associative carriers now sit in the
    typeclass hierarchy.  `CayleyAlgebra213.lean` (NEW, ~170 lines)
    is the Type A L3 file mirroring ZOmegaQuad/L4T bridge.
  · **Phase 4+ propext elimination across Types B + C** (commits
    `77f6daa`, `bd11810`): ZOmega tower and ZSqrt[D] tower elevated
    to strict ∅-axiom by:
      - replacing propext-leaking `simp only [add_comm, mul_comm,
        add_left_comm, mul_left_comm]` (Lean simp's congr machinery
        uses `Iff.mp` via propext) with safe-simp + explicit
        `Ring213.add_4_swap_mid` / new `add_6_interleave` / existing
        `Ring213.add_5_perm` reorder helpers + targeted
        `Int213.add_right_comm` swap sequences.
      - replacing propext-dirty stdlib lemmas `Int.sub_neg`,
        `Int.sub_zero`, `Int.zero_mul`, `Int.zero_add` with PURE
        `Int213.*` equivalents or `Int.sub_eq_add_neg + Int.neg_zero
        + Int.add_zero` decomposition.
    Cross-tower validation now COMPLETE — all three base towers
    strict ∅-axiom at every typeclass instance (Ring213, StarRing213,
    IntegerNormed213, MoufangIntegerNormed213, NonAssocRing213,
    NonAssocStarRing213):
      - Type A: ZI / Lipschitz / Cayley           [strict ∅-axiom]
      - Type B: ZSqrt[D] / L3T / L4T              [strict ∅-axiom]
      - Type C: ZOmega / ZOmegaDouble / ZOmegaQuad [strict ∅-axiom]
    The DRLT Validation Standard at the algebra layer holds at the
    strictest tier across the closed 4-row matrix.

**Phase 4 marathon — abstract Hurwitz extension foundations** (commits
`f22c741`, `d3b7132`, `e4a644a`, `54d8bce`): substantive progress on
the Cayley-Dickson Hurwitz extension at the framework level.
  · Two new axioms added to `IntegerNormed213`:
    - `normSq_conj : ∀ a, normSq (conj a) = normSq a` (norm is
      conj-invariant)
    - `ofInt_conj : ∀ z, conj (ofInt z) = ofInt z` (integer embeds
      are self-conj)
  · Generic `conj_mul_self : conj a · a = ofInt (normSq a)` derived
    from `self_mul_conj` + `conj_conj` + `normSq_conj`.
  · All 6 existing IntegerNormed213 instances (ZI / ZSqrt[D] / ZOmega
    / Lipschitz / ZOmegaDouble / L3T) extended with both new fields,
    verified STRICT ∅-axiom.
  · Eight abstract `cd_*` Hurwitz extension theorems proven at
    `[IntegerNormed213 α]` base in `CDDoubleStar.lean §7`:
      - `cd_ofInt`, `cd_normSq` (definitions)
      - `cd_self_mul_conj'`, `cd_ofInt_mul'`, `cd_ofInt_add'`,
        `cd_ofInt_inj'`, `cd_ofInt_central'`, `cd_normSq_conj'`
  · The cd_self_mul_conj' proof uses the generic `conj_mul_self`
    — establishing that the reverse self_mul_conj is the key
    missing piece for the abstract Hurwitz extension at non-comm
    associative bases.

**Phase 4 capstone (one architectural step remaining)**: direct
registration of `IntegerNormed213 (CDDouble α)` parametrically is
blocked by a typeclass diamond between
`CommStarRing213.toStarRing213` and `IntegerNormed213.toStarRing213`
when both are inferred for α (the parent `StarRing213 (CDDouble α)`
needs `CommStarRing213 α`, but `IntegerNormed213 α` also provides a
StarRing213 path).  Resolution requires a structural reorganization
(e.g., a `CommIntegerNormed213` combined typeclass that avoids the
diamond at instance time, or explicit instance disambiguation via
`@instStarRing213` qualifications).  The 8 abstract `cd_*` theorems
can already be invoked manually per concrete bridge to consolidate
Lipschitz/ZOmegaDouble/L3T's hand-written proofs (~100 lines each
→ 1-line projections).

Once the diamond is resolved, the generic `IntegerNormed213.normSq_mul`
derives Hurwitz at CDDouble α directly — fully replacing
`hurwitz_ring`-style polynomial expansion for the L2/L3 quaternion-
analog layer.  The L3/L4 alt layer (Cayley/ZOmegaQuad/L4T) requires
an additional step: the Moufang/alternative algebra version that
handles non-associativity.

Then Phases 5-6 (SHIFT RULE abstract functor + base-parametric
tower constructor).  Full plan in
`research-notes/G150_meta_cd_tower_subset.md` §"G150 Marathon —
Phase 진행".

## Intra-Lib/Math helper consolidation (#8a–#8f)

After the cross-ring extraction series (#6, #7) finished promoting
helpers *down* the ring stack (Lib/Math/Physics → Theory / Lens /
Meta), this series targets the same pattern **within Lib/Math
itself** — duplicates that have an existing canonical home one
helper-file away, not one ring away.

User directive: "lib/math 와 다른 링 뿐 아니라, lib/math 자체
내부에서도 이런 경우들이 있는지 조사해서 묶어보고 그 패턴을
조사해줘"  ("Investigate within Lib/Math itself for duplicates,
group them, and study the pattern.")

Constraint signalled mid-series: CD-tower modules (Cayley /
Sedenion / Trigintaduonion / Pathion `*Heavy.lean` + algebra
instance files) build slowly, so explicitly **deferred** from this
pass — focus on lighter sub-trees.

  · **#8a `binom_le_binom_succ`** — 2 files in
    `Lib/Math/Cohomology/Cup/` (KSubsetEraseIdx +
    FinBridgeGeneral) carried private inline copies of a
    1-cases-and-Nat.le_add_left Pascal-monotonicity lemma; the
    helper file `Combinatorics/Binomial.lean` already hosted
    `binom_n_0`, `binom_succ_2`, etc.  Promoted as a new public
    theorem and opened in both consumers.  Net: −28 lines.
  · **#8b `pow_mod_base`** — 2 files in
    `Lib/Math/Cohomology/Fractal/` (ConfigCountModular +
    ConfigCountAurifeuilleanParam) carried verbatim copies of
    `a^k % p = (a % p)^k % p`.  Promoted to
    `Meta/Nat/ModPow213.lean` as a Nat.pow-flavored sibling of
    the existing `modPow_mod_left` (no new dep — ModPow213
    already imports MulMod213).  Both consumers `open` it; no
    call-site changes.  Net: −29 lines / +26 lines.
  · **#8c `add_swap_two_mul`** — 2 files in `Lib/Math/Real213/`
    (Mobius213SternBrocot + Mobius213ContinuedFraction) carried
    verbatim 1-line `(a + b) + a = 2·a + b` Pseq-recurrence
    helper.  Promoted to `Meta/Tactic/NatHelper.lean` next to
    `add_mul` / `mul_assoc`.
  · **#8d `xor_pair_swap`** —
    `Cohomology/Bipartite/Parametric/EnrichedKNSNTc.lean` carried
    a private `xor_pair_swap` whose docstring literally read
    "Mirrors BoolXORFold.xor_pair_swap" — an explicitly-tagged
    duplicate of an already-public theorem.  Replaced with import
    + open.
  · **#8e `fin9LiftToNat` + `fin9LiftToNat_xor`** —
    V33Indeterminacy + V33c3Indeterminacy carried byte-identical
    `def vToNat (Fin 9 → Bool) : Nat → Bool` (~10 lines each) and
    `theorem vToNat_xor` (~11 lines each).  Promoted to
    `Infrastructure/BoolXORFold.lean` as `fin9LiftToNat` /
    `fin9LiftToNat_xor`; consumers use
    `open ... renaming fin9LiftToNat → vToNat, ...` to keep call
    sites verbatim.
  · **#8f delete unused `xor_false_right`** —
    `LeibnizLexListLevel.lean` carried a verbatim duplicate of
    `Cochain.Core.xor_false_right` that was *never used* — no
    internal call, no external open.  Deleted the dead leaf.

### Pattern findings (intra-Lib/Math)

1. **Helper-file under-utilisation**.  In #8a and #8b the
   canonical home (`Combinatorics/Binomial`, `Meta/Nat/ModPow213`)
   already existed and was already imported transitively by the
   consumer — but the consumers had local inline copies anyway.
   The bottleneck is **discoverability**, not API gaps.  Authors
   reaching for a helper writes it inline rather than searching
   for it.  Mitigation: when adding helpers, drop them in the
   existing topical home (Combinatorics/, Cohomology/Infrastructure/,
   Meta/Nat/) rather than the consumer file.
2. **Docstring-tagged duplication is the easiest fix**.  #8d's
   duplicate was self-flagged in the docstring as "Mirrors
   BoolXORFold.xor_pair_swap".  Pattern: `grep -rn "Mirrors\|same
   as\|copy of"` reliably surfaces author-acknowledged duplicates.
3. **Sibling-file duplicates dominate**.  Most pairs in #8 are
   between two files in the *same sub-tree* (Fractal/, Real213/,
   Bipartite/) doing similar things on different parameter slices.
   The pattern is "I'm writing a new instance file, let me copy
   the helper from the neighbour" rather than "let me promote it".
4. **Dead duplicates exist**.  #8f's `xor_false_right` was
   duplicated AND never used.  Local helpers tend to outlive their
   call sites because there's no usage-pressure to delete them.
   Worth a periodic `grep`-pass.
5. **Per-naming-style refactors are pervasive but heavy**.
   CD-tower files (`*Heavy.lean`, algebra instance files) have ~10
   duplicate primed helpers (`add_mul'`, `add_assoc'`, …) per
   ring level (ZI / Lipschitz / Cayley / Sedenion / …), but
   consolidating them requires moving them into a Ring213 typeclass
   utility module + heavy CD-tower builds.  Deferred per
   build-cost trade-off; structurally the cleanest fix is to define
   them once at the Ring213 typeclass level so every CD layer
   inherits.

Cumulative #8a–#8f: **2 new public theorems in
`Meta/Nat/ModPow213`, 1 new in `Meta/Tactic/NatHelper`, 1 new
public theorem + 1 new def in `Cohomology/Infrastructure/
BoolXORFold`, 1 new in `Lib/Math/Combinatorics/Binomial`**;
~120 lines of duplicated proof body removed across 9 consumer
files.  All `lake build` clean, all touched theorems
`#print axioms`-verified PURE.

## Cross-ring helper extraction in non-Physics rings (#7a–#7d)

Continued the helper-extraction work, applied to the
**Term / Theory / Lens** rings (per-user "Physics 제외한
다른 링들" request).

  · **#7a `nat_max_comm_pure`** — 2 files in the Lens ring
    (`Lens/Properties/ProdBelowId.lean` +
    `Lens/Instances/Reach.lean`) duplicated the same 14-line
    `Nat.max` commutativity proof.  Replaced with
    `open E213.Tactic.NatHelper renaming max_comm_pure → ...`
    (canonical version already in `Meta/Tactic/NatHelper`).
    Net: −28 lines.
  · **#7b `Raw.slash_ne_a` + `Raw.slash_ne_b`** — 3 files
    (`Lens/Number/Nat213/NumberingSystem`, `Lens/Instances/Reach`,
    `Lib/Math/Choice/CanonicalTruthChar`) duplicated
    `Raw.slash x y h ≠ Raw.b` under variant names using two
    different proof techniques (Tree.noConfusion vs Lens.depth).
    Promoted to `Theory.Raw.slash_ne_a` + `Theory.Raw.slash_ne_b`
    as protected public theorems in `Theory/Raw/Slash.lean`
    (alongside existing `slash_ne_{right,left,both}`).  Used the
    lightweight Tree.noConfusion proof (no Lens.depth import
    needed).  Net: −43 lines.
  · **#7c `Lens.leaves_view_ge_one`** — 2 files in the Lens
    ring duplicated `1 ≤ Lens.leaves.view r` proofs.
    `Lens.Congruence.leaves_view_pos` already proved the same
    but pulled in heavy `Number.Nat213.ChartGeneral`.  Added a
    lightweight protected `Lens.leaves_view_ge_one` directly
    in `Lens/LensCore.lean` (next to the `Lens.leaves`
    definition).  Bonus: the 5 ModArith files from #6b switched
    to the lighter version, dropping Number/Nat213 deps.
    Net: −23 lines + lighter import graph downstream.
  · **#7d `xor_comm`** — added `xor_comm` to `BoolHelper.lean`
    (alongside `bool_eq_iff` from #6a).
    `Lens/Instances/Parity` consumed it.  Net: −2 lines + a
    repo-wide `Bool.xor_comm` replacement now available.

Cumulative #7a–#7d: **2 new public theorems in
`Theory/Raw/Slash`, 1 in `Lens/LensCore`, 1 in
`BoolHelper`**; ~96 lines removed across non-Physics rings.
All `lake build` clean.

## Cross-ring helper extraction (#6a–#6f)

Per-user request to find Lib/Math files repeatedly proving the
same private helper and promote it to a lower ring (Meta/Lens)
where it can be shared.  Six sub-cleanups, each independently
committed:

  · **#6a `bool_eq_iff`** — 12 Lib/Math files each defined the
    same 8-line `Bool` extensionality lemma under variant names
    (`bool_eq_iff{|_v2|_local}`, `bool_eq_of_iff_true{|_v3|'}`).
    Created `Meta/Tactic/BoolHelper.lean` as the canonical
    source.  Each consumer reduces to `import ... + open`.
    Net: −80 lines.
  · **#6b `leaves_ge_one`** — 5 `Lib/Math/ModArith/Join*.lean`
    files duplicated `1 ≤ Lens.leaves.view r` (~12 lines).
    Replaced with `open E213.Lens renaming leaves_view_pos →
    leaves_ge_one(_local)` — `Lens.Congruence.leaves_view_pos`
    already existed as the canonical public theorem in the
    Lens ring.  Net: −55 lines.
  · **#6c `sub_pos_of_lt_213`** — 4 DyadicFSM files duplicated
    `a < b → 0 < b - a` under `_213`/`_local` suffixes (~7 lines
    each).  Replaced with `open E213.Tactic.NatHelper renaming
    sub_pos_of_lt → ...` — already canonical in `Meta/Tactic/NatHelper`.
    Net: −24 lines.
  · **#6d `one_le_two_pow` + `succ_le_two_pow`** — 4 Lib/Math
    files duplicated the standard power-of-2 lower bounds
    (15–22 lines each).  Added both as canonical theorems in
    `Meta/Tactic/Pow213.lean`.  Net: −60 lines (+25 in
    `Pow213`).
  · **#6e `one_le_of_ne_zero`** — 2 `Lib/Math/Irrational/*` files
    duplicated `k ≠ 0 → 1 ≤ k` (5 lines).  Added to
    `Meta/Tactic/NatHelper`.  Net: −10 lines.
  · **#6f `pair_encoded_lt`** — 2 `Lib/Math/DyadicFSM/ArithFSM/`
    files duplicated `b · n + c < n²` for `Fin n` pairs (11 lines).
    Added to `Meta/Tactic/Fin213`.  Net: −20 lines.

Cumulative #6a–#6f: **3 new Meta/Tactic theorems +
1 new Meta/Tactic/BoolHelper.lean**, **29 private duplicates
removed** across Lib/Math.  All cleanups full `lake build` clean.

## Autonomous cleanup marathon

Continuing the duplication-removal pass from #3/#4.  Five
sub-cleanups (#5a–#5e), each independently committed:

  · **#5a Pisano predictor chain** (9 → 1 file).
    `Pisano/Predictor{6,7,8,11,14,17,20,22,23}.lean` formed a
    layered enumeration where each Predictor_N re-packaged the
    prior milestone + one new `pisano_period_lift` call.  Final
    proof in `Predictor23.lean` chained `H.2.2.2...` 22 levels
    deep.  Consolidated to `PredictorChain.lean` with 23
    per-prime lemmas (each a 3-line `pisano_period_lift` call)
    plus two convenience conjunctions (`_7` for downstream
    consumers, `_23` headline).  Net: −725 lines.
  · **#5b Hodge Δ⁴ prop-lifts** (5 → 1 file).
    `Hodge/Prop, Prop50, Prop52, Prop53, Prop54.lean` each
    lifted "⋆⋆ = id" to Prop-level at one (5, k) stratum.  Four
    of them used the identical COH-2 template (3 private
    `decide`-lemmas + 5-line capstone).  Consolidated to
    `InvolutionLifts.lean` covering all five strata plus the
    all-strata bundle; `InvolutionCapstone.lean` retained as
    backward-compat shim.  Net: −81 lines.
  · **#5c Pell Lens compositions** (3 → 1 file).
    `Pell/Lens.lean (3x5)`, `LensPairs.lean (3x7 + 5x7)`,
    `LensTriple.lean (3x5x7)` collapsed to
    `LensCompositions.lean` with all CRT closures + the BitFSM-
    form period lifts in one place.  Net: −33 lines.
  · **#5d Trib CRT capstones** (2 → 1 file).
    `Trib/CRTCapstone.lean (3-mod)` and `CRT4Capstone.lean
    (4-mod)` merged into a single `CRTCapstone.lean` with both
    `trib_crt_capstone` and `trib_crt_4_capstone`.  Net: −25
    lines.
  · **#5e Catalan extension** (2 → 1 file).
    `Combinatorics/CatalanExtended.lean` (recursion witnesses
    for n = 5, 6, 7) merged into `Catalan.lean` (which had
    n = 3, 4).  Net: −22 lines.
  · **#5f ZSqrt[-2] deeper tower** (3 → 1 file).
    `ZSqrtMinus2TowerL{7,8,9}.lean` (each a sequential
    CD-doubling: 64/128/256 units) merged into
    `ZSqrtMinus2TowerDeep.lean` — leaf chain not imported by
    the CayleyDickson umbrella.  Net: −84 lines.
  · **#5g Hurwitz Type D tower** (2 → 1 file).
    `HurwitzTowerL{1,2}.lean` (48/96 units in Type D Hurwitz
    CD-doubling) merged into `HurwitzTower.lean`.  Same
    pattern as #5f.  Net: −37 lines.
  · **#5h CupAW bz5_<n> bridges** (3 → 1 file).
    `Leibniz21Bridge.lean (bz5_1)`, `Leibniz22Bridge.lean
    (bz5_2)`, `Leibniz5_3_1Bridge.lean (bz5_3)` each provided
    the identical 2-theorem `_false_at` / `_true_at` pattern
    at strata `n ∈ {1, 2, 3}`.  Merged into `LeibnizBzBridge.lean`
    with all 6 theorems; downstream consumers' imports +
    opens updated via sed.  Net: −41 lines.
  · **#5i LeibnizAlgLift Alpha corollaries** (2 → 0 files).
    `LeibnizAlgLift21Alpha.lean` and `LeibnizAlgLift22Alpha.lean`
    were 41-line single-theorem corollary files specialising
    `LeibnizAlgLiftAlpha.leibniz_via_α_decomp_general` at
    `b = 1, 2`.  Both moved as named theorems into
    `LeibnizAlgLiftAlpha.lean`.  Also added explicit
    `LeibnizAlgLift{21,22}` imports to
    `Leibniz{21,22}Final.lean` (previously transitive via the
    deleted Bridge chain).  Net: −44 lines.
  · **#5j orphan `basis_leibniz_5_3_1`** (1 file → 0).
    `Leibniz5_3_1Basis.lean` was a 36-line single-theorem
    orphan with zero consumers, sister of
    `basis_leibniz_5_2_1` which lives in `BasisLeibniz.lean`.
    Theorem moved into `BasisLeibniz.lean`.  Net: −26 lines.
  · **#5k CupAtomic 3-file chain** (3 → 1).
    `CupAtomic.lean` (d = 5 case), `CupAtomicExtended.lean`
    (d ∈ {3, 4}), `CupAtomicGeneralD.lean` (∀d closed form
    `count(d) = d · 2^(d+1)`).  Three leaf files with no
    external consumers.  Merged into `CupAtomic.lean` as §1–6.
    Net: −107 lines, 38 PURE theorems consolidated.
  · **#5l `EncodingBijection52` → `EncodingBijection`** (2 → 1).
    Two sibling files for (5, 1) and (5, 2) cochain ↔ Fin
    encoding bijections.  Merged with both sub-namespaces
    preserved so consumer fully-qualified names
    (`EncodingBijection.encode_5_1` /
    `EncodingBijection52.encode_5_2`) keep resolving.
    Net: −10 lines.
  · **#5m orphan `CutExpODE`** (1 → 0).  47-line zero-consumer
    file with 2 theorems that were pure renames of
    `CutExpSeries`'s `expPartialSum_zero` / `_succ`.  Deleted.
    Net: −47 lines.
  · **#5n `LeibnizLex21` → `LeibnizLexSelfRef`** (1 → 0).
    97-line orphan extending the self-referential twisted
    Leibniz from bidegree (1, 1) to (2, 1).  Merged as §3.
    Net: −27 lines.
  · **#5o orphan `SelfRefDepthExtended`** (1 → 0).  92-line
    zero-consumer file with d ∈ {6, 7, 8} validation data.
    Merged as a new section in `SelfRefDepth.lean`.  Net: −19
    lines.

Cumulative across #5a–#5o: **36 files deleted, 8 new files
created, net −1328 lines**.  All cleanups full `lake build`
clean (cleaned-cache rebuild verified for #5h+#5i, which had
been masked by stale `.olean` cache during the original
single-module audit).  All touched modules verified PURE by
`scan_axioms.py`.

Remaining inspected-but-not-consolidated candidates:
  · `Cohomology/Universal/Prop{31,41,42,51,52,53,54}.lean` —
    layer-enumeration but heavily consumed by `CupAW/Leibniz*`
    via per-arity `pattern_eq_at`; namespace move would
    require many find/replace operations.
  · `Real213/{Int,Half,Third,Fifth}ValidCut.lean` — research
    progression milestones, each a different proof phase.
  · `Cohomology/Bipartite/Filled{3,4,5}CellExtension.lean` —
    sequential dimension extensions with unique math per layer.
  · `Lib/Physics/AlphaEM/FractalLevelZeta*.lean` — C5
    research-step chain, sequentially numbered.

Each was assessed: the file naming smells of layer-enumeration
but the content per file is either genuinely unique math or
the consumer impact of consolidation outweighs the file-count
saving.

## Previous session — Cleanup pass #4: 5 enrichments → 1 unified bipartite carrier

Five domain-flavoured enrichments (`WalkEnrichment`,
`CochainEnrichment`, `HoTTEnrichment`, `HigherAlgebraEnrichment`,
`AnalysisEnrichment`) were line-for-line identical modulo
cosmetic renaming (field name `length` / `degree` / `level` /
`exponent`; constructor labels; operation labels `concat` /
`cup` / `suspend` / `day` / `compose`).  All consolidated to a
single parametric file.

The unified core:

```lean
namespace E213.Lib.Math.GRA.Enrichment

structure BipartiteCarrier where
  n : Nat
  constraint : n = 0 ∨ n ≥ 2

def BipartiteCarrier.{zero, two, three} : BipartiteCarrier := ...
def BipartiteCarrier.combine : BipartiteCarrier → BipartiteCarrier → BipartiteCarrier
def GRA23_Bipartite : GRAModel := ...
def forgetHom : GRAHom GRA23_Bipartite GRA23_NT := ...
```

The domain naming (Walk-length / Cochain-degree / Truncation-
level / Operad-level / Resolution-exponent) was commentary on
what `n` *interprets as*, not mathematical content.  The
arithmetic is one structure.

Consumers also collapsed their 5-fold sections to one:

  · `LensBridge.lean` — 5 `*GradeMap` definitions → 1
    `bipartiteGradeMap`; 5 atom-realize lemmas → 1 pair
  · `CarrierRealization.lean` — 5 `*Realize` defs → 1
    `bipartiteRealize`; 5 atom theorems → 1 pair; 5 slash
    theorems → 1
  · `Naturality.lean` — 5 `*_depth_natural` theorems → 1
    `bipartite_depth_natural`; 5 `*ToNT` homs → 1
    `bipartiteToNT`; `DepthNaturality` record from 5 fields → 1
  · `SectionRetraction.lean` — 5 `*.section` definitions → 1
    `Bipartite.section`; 5 retraction lemmas → 1 pair;
    `WalkRetract` → `BipartiteRetract`
  · `Universality23.lean` — 5 `*GradeMap_forced` → 1
    `bipartiteGradeMap_forced`; 5 `*Realize_grade_forced` → 1
  · `LensIsoCapstone.lean` — 5 `*Realize_grade_eq_lens` → 1

Deleted (full history preserved in `git log`):
  · `lean/E213/Lib/Math/GRA/WalkEnrichment.lean` (165 lines)
  · `lean/E213/Lib/Math/GRA/CochainEnrichment.lean` (133)
  · `lean/E213/Lib/Math/GRA/HoTTEnrichment.lean` (128)
  · `lean/E213/Lib/Math/GRA/HigherAlgebraEnrichment.lean` (116)
  · `lean/E213/Lib/Math/GRA/AnalysisEnrichment.lean` (117)

New: `lean/E213/Lib/Math/GRA/Enrichment.lean` (~145 lines, 11 PURE).

Net effect: GRA sub-tree went from 26 → 22 files; ~4700 → ~3500
lines; PURE-theorem count dropped (5-fold dup theorems collapsed
to 1 each) but coverage is unchanged.

Build verified: `lake build` clean (1004/1004); per-module
`scan_axioms.py` reports all 7 touched modules **all PURE**.

Docs updated: GRA.lean umbrella, THEORY_BOOK Part VI.6 + VI.7,
gra_book.md preamble, gra_as_substrate essay §2 + §3 + Phase 17
paragraph, STRICT_ZERO_AXIOM Tier 5.1 Phases 11–18 entries.

## Previous step — Cleanup pass #3: `HasDistinguishing` consolidation

Three exploratory Phase-19/20/21 typeclasses (`HasDistinguishingU`,
`HasDistinguishingW`, `HasDistinguishingWFull`) consolidated into a
single universe-polymorphic typeclass `HasDistinguishing213.{u, v} α`.

Per user directive: *"제네럴라이즈 할수있음 하는게 좋다구 생각행 /
지금까지는 정확히 어떤 모양으로 만들어야하는지 몰라서 탐색하기 위해
이렇게 엄청 많이 정리들을 만들어온거지만, gra라는 모양으로 기술할 수
있어졌으니깐?"* — the exploration phase is over; now that we can
describe the structure in GRA-shape, generalise where possible.

The unified typeclass:

```lean
structure HasDistinguishing213.{u, v} (α : Type u) where
  a, b : α
  combine : α → α → α
  Equiv : α → α → Sort v
  refl/symm/trans
  combine_sym : ∀ x y, Equiv (combine x y) (combine y x)
  distinct_equiv : Equiv a b → False
```

Setting `Equiv := Eq` recovers the strict form (Phase 19); setting
`Equiv := GRAIso` recovers the categorical form (Phase 20–21).
Two closed instances exhibit both:

  · `liftedReadingHasDistinguishing213 : HasDistinguishing213.{1, 0}
    (ULift.{1, 0} Reading)` — strict case at `Type 1` via ULift.
  · `gra23HasDistinguishing213 : HasDistinguishing213.{1, 1} GRA23` —
    categorical case with `productSwapIso` + `trivial23_not_iso_NT`.

Deleted (full history preserved in `git log`):
  · `lean/E213/Lib/Math/GRA/Universe1.lean`
  · `lean/E213/Lib/Math/GRA/HasDistinguishingW.lean`
  · `lean/E213/Lib/Math/GRA/HasDistinguishingWFull.lean`

New: `lean/E213/Lib/Math/GRA/HasDistinguishing213.lean` (23 PURE).

Build verified: `lake build E213.Lib.Math.GRA` clean;
`scan_axioms.py E213.Lib.Math.GRA.HasDistinguishing213` reports
**23/23 PURE**.

Docs updated:
  · `lean/E213/Lib/Math/GRA.lean` umbrella docstring (Phases 19–21
    section merged + PURE count updated)
  · `theory/THEORY_BOOK.md` Part II.5 + Part VI.8
  · `theory/math/gra_book.md` summary preamble
  · `theory/essays/gra_as_substrate_of_cat_hott.md` Phases 19–21
    paragraph rewritten
  · `STRICT_ZERO_AXIOM.md` Tier 5.1 Phases 19–21 entry

## Previous step — Cleanup pass #2: legacy doc archives (guide/ + books/math/)

INDEX-audit pass revealed two **fully stale narrative
directories** referencing dead Lean paths:

  · `guide/` (~1100 lines, 16 chapters) — self-described as
    "transitional bridge" before reorganisation; referenced
    `lean/E213/Research/` (non-existent) and `framework/E213/`
    (non-existent).  Functionally superseded by
    `theory/THEORY_BOOK.md`.
  · `books/math/` (6 narrative volumes, ~2700 lines):
    `analysis213.md`, `cohomology-213.md`, `linalg-213.md`,
    `number-theory-213.md`, `probability-213.md`,
    `universal-lens-213.md`.  All reference dead path
    `lean/E213/Research/Real213/*.lean` (current path is
    `lean/E213/Lib/Math/Real213/`).

Both archived to `research-notes/archive/legacy_docs/{guide,
books_math}/` via `git mv` (full history preserved).  Git can
recover any unique content if needed.

6 active external references updated:
  · `seed/INDEX.md` line 163 — `guide/INDEX.md` →
    `theory/THEORY_BOOK.md`
  · `seed/ORIGIN.md` line 110 — same
  · `seed/AXIOM/09_lean_correspondence.md` line 125 —
    `guide/` + `books/` → `theory/THEORY_BOOK.md` + theory/*
  · `README.md` line 184–198 — `books/math/` block replaced
    with `theory/THEORY_BOOK.md` + per-area pointer
  · `lean/E213/INDEX.md` line 3 — entry-point list updated
  · `LESSONS_LEARNED.md` lines 271–272 — guide chapter
    references rewritten to THEORY_BOOK Part I/II/VIII

Remaining references (in `research-notes/G35_*`, archive/
audits) left as historical context — they live in scratchpad
/ archive and don't need active maintenance.

Net effect:
  · ~3800 lines of stale narrative removed from active tree
  · 3 doc sources (THEORY_BOOK + books/ + guide/) → 1
    (THEORY_BOOK)
  · No Lean code touched

## Previous step — Cleanup pass #1: GRA narrative consolidation

`theory/math/graded_residue_arithmetic.md` (Korean synthesis,
430 lines) consolidated into `theory/math/gra_book.md`
(English textbook) — the two files covered the same content in
two languages, violating CLAUDE.md "repo artifacts English
only" discipline.

Unique content absorbed into `gra_book.md`:
  · Ch.8.5 — GRA × Algebra213 (`GradedRing213` typeclass
    sketch + CD tower grade table + det=1 trinity in algebraic
    vocabulary)
  · Ch.8.6 — Dimensional proliferation fractal
    (`C(5,3) = 10` direction self-similarity + det=1 volume
    preservation)
  · Ch.8.7 — Periodic structure: mod-p and Adelic decomposition
    (`P⁵ ≡ −I (mod 5)` + Adelic GRA conjecture)
  · Ch.9 — One-paragraph master statement (the `det=1 /
    gcd=1 / Frobenius=1` trinity + GRA Tower ↔ CD Tower duality)

Source file `graded_residue_arithmetic.md` archived to
`research-notes/archive/G148_graded_residue_arithmetic_synthesis.md`
via `git mv` (history preserved).

References updated (6 sites):
  · `theory/THEORY_BOOK.md` Part VI intro
  · `theory/math/INDEX.md` Universal-meta-structure
    section: "(2)" → "(1)" + single chapter
  · `theory/essays/INDEX.md` gra_universality essay row
  · `lean/E213/Lib/Math/GRA.lean` umbrella docstring
  · `lean/E213/ARCHITECTURE.md` Lib/Math/GRA description
  · `research-notes/INDEX.md` G149 lifecycle note

No Lean code touched (doc-only consolidation; build unchanged).

## Previous step — Theory Book v1.2 expansion + structure cleanup

`theory/THEORY_BOOK.md` v1.2 — physics removed (will be written
once mathematical derivation closes completely), book expanded
to **1216 lines** (was 878) via 5-agent comprehensive sweep of
`seed/`, `theory/`, `lean/E213/` finding ~60 substantive
missing items.  High-impact additions integrated:

  · Part I.4 — full self-completion thesis (4-clause
    simultaneous visibility)
  · Part I.7 — encoding costs + cmp-independence meta-theorem
  · Part I.8 (new) — **Six-theorem: 10 readings of 6** as
    one Raw event
  · Part II.1 — Eqv (Raw-internal congruence) +
    parenthesization distinctness
  · Part II.4 — Lens.Initiality + Lens.Universal.QuotLens +
    Lens.Compose suite + Lens.Algebra/Lattice
  · Part II.6 (new) — RawTopology bookends + Bool213
  · Part II.7 (new) — Flat ontology + syntactic
    internalisation + predicate self-encoding
  · Part II.8 (new) — Cardinality as Lens-observable family
    (Cantor / Tower / Godel / Pair / etc.)
  · Part III.6 (new) — Atomicity correspondence (d = 5 at
    inductive-type level)
  · Part III.7 (new) — Bit-pattern uniqueness
  · Part IV.1 — Three mediant Tower lifts
    (NatPair→Int/QPos, NatTriple→Z2 with Eisenstein
    `1 + ω + ω² = 0`)
  · Part IV.2 — **Mobius213GrandUnification 10-conjunct
    master** + AtomicityAnchor + SternBrocotReachable
  · Part V.1 — Five-direction c-counter (A/B/C/D/E) detail
    + cross-graph universality
  · Part V.8 (new) — ParadigmDomain 9-domain unification
  · Part V.9 (new) — Algebra213 / Ring213 / HurwitzRing
  · Part V.10 (new) — Aurifeuillean fractal `N_U + 1`
  · Part V.11 (new) — H³ / H⁴ stable at +6
  · Part VIII.5 — Propext-avoidance pattern set (12
    patterns)
  · Part VIII.6 (new) — PatternCatalog atomic games
  · Part VIII.7 (new) — Proof-shape fingerprinting + L1
    parametric extraction
  · Part VIII.8 (new) — Falsifiability operationalised
    (135 + 26 falsifiers)
  · Part VIII.9 (new) — Scanner archetypes

### Structure cleanup applied (from audit agent)

  · `theory/essays/INDEX.md` — added missing
    `every_axis_sees_p.md` entry
  · `theory/INDEX.md` — chapter count updated from
    "120 total, incl. 24 essays" to "~138 total, incl. 27
    essays"
  · `research-notes/INDEX.md` — added 5 active Tier-1 notes
    (G121, G123, G135, G136, G149) to registry with
    lifecycle status

### Sweep methodology

5 parallel `Explore`-agents:
  1. Foundations/Lens (seed/AXIOM + lean/E213/{Theory/Raw,
     Lens})
  2. Number systems (Nat213, Real213, Padic, Mobius213,
     CayleyDickson)
  3. Algebra & cohomology (Cohomology, HodgeConjecture,
     DyadicFSM, ParadigmDomain)
  4. Methodology + essays + meta-infrastructure
  5. Structure cleanup audit (background async)

Each agent read assigned files deeply; total findings
catalogued for selective integration.  High-impact items
integrated; lower-impact items remain in agent transcripts
for future expansion.

## Previous step — Theory Book v1 (878 lines)

`theory/THEORY_BOOK.md` v1 — single linearised reading path
from `seed/AXIOM/` to GRA Phase 22's `Lens.Unified` capstone.
Synthesises the 148-chapter `theory/` catalog + Lean docstrings
into nine parts:

  · Part 0 — Preface (what the book is + reading conventions)
  · Part I — Axiom + substrate (`seed/AXIOM/` 9 chapters)
  · Part II — Raw, Lens, HasDistinguishing
  · Part III — Atomic forcing `(NS, NT, c, d) = (3, 2, 2, 5)`
  · Part IV — Number systems forced from Raw + P (Nat213,
    Möbius P, CD tower, Real213, Padic)
  · Part V — Algebraic + cohomological structure
    (K_{NS, NT}^{(c)}, Stern-Brocot, Hodge, Sym(3), universe
    chain)
  · Part VI — GRA universality (Phases 1–22 condensed)
  · Part VII — Physics deployment (α_em, gluon octet,
    Validation Standard)
  · Part VIII — **Foundational frameworks as Readings**
    (Peano / ZFC / classical-analysis / HoTT / Cat all as Lens
    compositions over Raw; `lean/E213/Lib/Math/AxiomSystems/`
    + Phase 22 capstone)
  · Part IX — Methodology + discipline (three-tier,
    strict ∅-axiom, scanner suite, failure modes)
  · Appendices — Lean source map, notation, glossary,
    companion documents, reading paths

The book is a **navigational + synthesis document**, not
content-replicated.  Each section cites theory/ chapters and
Lean modules; the synthesis paragraphs at part boundaries pull
cross-frame insights.

Linked from `theory/INDEX.md` "Top-level orientation".

## Previous step — Phase 22: Lens.Unified × GRA capstone (401 PURE)

One new file extending GRA from 27 → 28 files, 374 → 401 PURE.

  · **Phase 22 `LensIsoCapstone.lean`** (27 PURE) — the deepest
    213-native statement of GRA's content.  Connects GRA's
    canonicalGradeMap (Phase 16) and its universal property
    (Phase 18) to `Lens.Unified.LensIso` (the 213-native
    equivalence concept on Lenses).
      · `gradeLens : Lens Nat := ⟨2, 3, (· + ·)⟩` is the
        canonical 213 Lens.  `gradeLens.view r = Raw.fold 2 3
        (· + ·) r = canonicalGradeMap r` by definitional
        unfolding.
      · `profile_view_eq_canonical` lifts Phase 18 to Lens
        vocabulary.
      · `profile_lens_LensIso_gradeLens` — **the headline**:
        every (2, 3)-profile Lens on Nat is `LensIso` to
        `gradeLens`.  Proof via `Lens.Unified.lensIso_iff_kernel_eq`.
      · `walkLens` / `cochainLens` / `truncationLens` /
        `operadLens` / `resolutionLens` — five Reading Lens
        defs (definitionally `gradeLens`); each `*Lens_LensIso`
        theorem confirms membership.
      · `*Realize_grade_eq_lens` (five) — Phase 17 realizations
        project to `gradeLens.view` by `rfl`.
      · `gra_lens_iso_class_capstone_holds` — the bundle of
        universal property + 5 Reading `LensIso`s.

The (2, 3)-arithmetic forced by atomic distinguishing IS the
`LensIso` equivalence class of `gradeLens` — the strongest
formal statement of GRA's relation to Raw.  All five Readings
are explicit class members; the universal property forces any
future (2, 3)-Reading into the same class.

## Previous step — Phase 21: full HasDistinguishingWFull on GRA23 (374 PURE)

One new file extending GRA from 26 → 27 files, 362 → 374 PURE.

  · **Phase 21 `HasDistinguishingWFull.lean`** (12 PURE) — closes
    the categorical-distinctness leg of the Cat-as-Reading
    frontier.
      · `HasDistinguishingWFull.{u, v}` — extends Phase 20's
        `HasDistinguishingW` with `distinct_equiv : Equiv a b →
        False`.  Type-valued because `Equiv` is Type-valued.
      · `trivial23_not_iso_NT` — **the headline cardinality
        proof**.  Any would-be `GRAIso trivial23 GRA23_NT` gives
        `iso.invFun : Nat → TrivialCarrier`, but `TrivialCarrier`
        is a subsingleton (proved by `cases x; cases y; rfl`),
        so `iso.invFun 0 = iso.invFun 1`.  `right_inv` then
        forces `0 = iso.toFun (iso.invFun 1) = 1`, contradicting
        `decide 0 ≠ 1`.
      · `gra23HasDistinguishingWFull : HasDistinguishingWFull.{1, 1}
        GRA23` — the full instance.  Atoms `trivial23` (1-element
        carrier) and `GRA23_NT` (Nat carrier); combine =
        `Monoidal.product`; Equiv = `GRAIso` on underlying
        models; refl/symm/trans from Phase 7; combine_sym from
        Phase 20's `productSwapIso`; distinct_equiv from the
        cardinality proof.
      · `hasDistinguishingWFull_witness` — `Nonempty` existence
        statement.

The categorical "Cat-as-Reading of GRA" content is now a full
Lean theorem at `Type 1`: there exists a categorically-distinct
HasDistinguishingW structure on a `Type 1` carrier with natural
combine, iso-symmetric combine_sym, and categorical
distinctness.  The Phase 17/18/19/20/21 chain closes every leg
of the essay's frontier.

PURE: uses only `cases` on TrivialCarrier (the structural
subsingleton fact), iso's `right_inv` axiom (definitional),
and `decide` on Nat literal inequality.  No propext, no
Classical, no Mathlib.

## Previous step — Phase 20: iso-symmetric natural combine_sym (362 PURE)

One new file extending GRA from 25 → 26 files, 357 → 362 PURE.

  · **Phase 20 `HasDistinguishingW.lean`** (5 PURE) — the natural
    iso-symmetric combine question that Phase 19's strict
    combine could not capture.
      · `HasDistinguishingW.{u, v}` typeclass — like Phase 19's
        `HasDistinguishingU` but with `combine_sym` taking values
        in a `Sort v`-valued `Equiv` relation instead of strict
        `=`.  Refl/symm/trans of `Equiv` are required.
      · `productSwapIso` — the headline construction.  For any
        two (2, 3)-GRA models `M₁`, `M₂` (with the parameter
        hypotheses), gives a `GRAIso` between
        `Monoidal.product M₁ M₂` and `Monoidal.product M₂ M₁`.
        Underlying map is pair-swap `(a, b) ↦ (b, a)`.
        `grade_comm` discharges by `Nat.add_comm`;
        `oplus_comm`/`otimes_comm` by `cases p; cases q; rfl`.
      · `product_combine_sym_witness` — packages the swap iso
        as the witness "monoidal product is iso-symmetric".
      · `productSwapIso_involutive` — swap is self-inverse at
        the function level.
      · `product_grade_sym` — additive grade symmetry.
      · `product_combine_sym_at` — the swap iso restated as
        the combine_sym component of a `HasDistinguishingW`
        instance.
  · Combined with Phase 7's `GRACat` and Phase 15's
    `Monoidal.product`, this completes `GRACat` as a *symmetric
    monoidal category* with `productSwapIso` as the braiding.

Essay updated: Phase 20 closes the natural-combine question
("natural combine on Cat-objects is iso-symmetric, not strict").
The two-phase pair (Phase 19 strict + Phase 20 weak) covers
both the universe-lifting existence demonstration and the
natural-combine content question.

## Previous step — Phase 19: strict 2-cat universe-lifting (357 PURE)

One new file extending GRA from 24 → 25 files, 342 → 357 PURE.

  · **Phase 19 `Universe1.lean`** (15 PURE) — the strict
    2-categorical universe-lifting frontier from Phase 18.
      · `HasDistinguishingU.{u}` — universe-polymorphic parallel
        of `Lens.SemanticAtom.HasDistinguishing` (which is fixed
        at `Type 0`).
      · `Reading` enum (from Phase 7) is enriched with `deriving
        DecidableEq` so strict-equality tests work PURE.
      · `readingCombine r s := if r = s then r else .NT` is
        strictly commutative (the condition `r = s` is symmetric;
        proof closes by `by_cases`).
      · `readingHasDistinguishingU : HasDistinguishingU.{0} Reading`
        — instance at `Type 0` with atoms `NT`, `Graph` and the
        strict-commutative combine.
      · `liftedReadingHasDistinguishingU : HasDistinguishingU.{1}
        (ULift.{1, 0} Reading)` — **the strict 2-cat statement**:
        a `Type 1` carrier admits the distinguishing structure.
        Lifts atoms via `ULift.up` and combine via
        `liftedCombine r s := ULift.up (readingCombine r.down
        s.down)`.
      · `reading_atomic_agreement` — the lifted carrier's atomic
        grade map matches `canonicalGradeMap` at `Raw.a` and
        `Raw.b` (both `rfl`), so the (2, 3)-profile is preserved.
      · `universe1_distinguishing_witness` — the capstone
        delivering the `Type 1` instance.
  · This meets the strict 2-categorical universe-lifting
    requirement Phase 18 named.  The `Type 1` carrier exists
    with the distinguishing structure; the parameterless
    arithmetic discipline is not broken by universe lifting.

Essay updated: open frontier shifts from "strict 2-cat" (closed)
to "natural-combine on Cat-objects requires iso-symmetric
combine_sym, a weakening of `HasDistinguishingU`" — the
*content* of "Cat-Lens" beyond Phase 19's universe-lifting
demonstration.

## Previous step — Phase 18: universal property, 1-cat proxy for GRACat-as-Cat (342 PURE)

One new file extending GRA from 23 → 24 files, 329 → 342 PURE.

  · **Phase 18 `Universality23.lean`** (13 PURE) — the parameterless
    forcing statement at the Raw level.
      · `canonicalGradeMap_universal` — any `f : Raw → Nat` with
        `f Raw.a = 2`, `f Raw.b = 3`, slash-additive equals
        `canonicalGradeMap` pointwise.  Proof: Raw induction.
      · Specialised: each enrichment's grade map (`walkGradeMap`,
        `cochainGradeMap`, `truncationGradeMap`, `operadGradeMap`,
        `resolutionGradeMap`) is derived as an instance of the
        universal property — `*_forced` theorems.
      · Realization-level forcing: `walkRealize_grade_forced` etc.
      · `two_atoms_slash_agree` — two such functions agree pointwise.
      · Capstone `canonical_arithmetic_forced` — the parameterless
        forcing statement.
  · This is the 1-categorical proxy for the essay's "GRACat-as-Cat
    is a Reading" frontier.  The strict 2-categorical statement
    requires `HasDistinguishing` on `Cat`-objects, which needs
    universe lifting — outside the parameterless-arithmetic
    discipline.  The universal property captures the conceptual
    content: ANY structure (Cat-object included) whose grade map
    satisfies the (2, 3)-profile is forced to read the canonical
    arithmetic.

Essay updated: "Open beyond Phase 18" section names the strict
2-categorical statement as the remaining open question, with the
explanation that the 1-categorical content has been captured.

## Previous step — Phase 17: carrier realization, closes Phase 16 frontier (329 PURE)

One new file extending GRA from 22 → 23 files, 296 → 329 PURE.

  · **Phase 17 `CarrierRealization.lean`** (33 PURE) — closes the
    open frontier named in
    `theory/essays/gra_as_substrate_of_cat_hott.md` (the carrier-
    level Lens equation between enrichments).  Key lemma
    `canonical_ge_2 : ∀ r : Raw, canonicalGradeMap r ≥ 2` (Raw
    induction: atoms → 2 or 3, slash → sum of ≥-2 values ≥ 4)
    enables direct construction
    `walkRealize r := ⟨canonicalGradeMap r, Or.inr (canonical_ge_2 r)⟩`
    (and the same shape for cochainRealize / truncationRealize /
    operadRealize / resolutionRealize).  This *bypasses* the
    enriched `Raw.fold` route — no `combine_sym` proof needed
    for the Prop-field-carrying carriers (which would force
    structural equality with `propext`).
  · Each realization's grade-projection equals `canonicalGradeMap`
    by `rfl`; all pairwise carrier-level agreement theorems
    (including the headline `truncation_operad_realize_agree`,
    the HoTT ↔ Higher Algebra equation at the carrier level)
    follow by `rfl`.
  · Atom and slash behavior at the carrier level: `*_realize_a`,
    `*_realize_b`, `*_realize_slash` for all five realizations.

The essay's open frontier section was rewritten to mark this
closure, with a brief explanation of the bypass strategy.

## Previous step — Phase 16: Lens bridge + essay (296 PURE)

One new file + one new essay extending GRA from 21 → 22 files,
259 → 296 PURE:

  · **Essay `theory/essays/gra_as_substrate_of_cat_hott.md`** —
    "Could GRA play the role Category theory / HoTT normally
    occupy, but from a more fundamental position?"  The (2, 3)
    arithmetic is parameter-forced by atomic distinguishing;
    Cat and HoTT carry external design choices (universe, ∞-cat
    doctrine).  Hence the forcing direction is GRA → Cat/HoTT,
    not Cat/HoTT → GRA.  Companion to
    `gra_universality_one_principle.md`.
  · **Phase 16 `LensBridge.lean`** (37 PURE) — the canonical
    Raw-level grade map `canonicalGradeMap := Raw.fold 2 3 (· + ·)`,
    the PURE backbone of "(2, 3)-arithmetic at the Raw level".
    All five enrichment grade maps (walk / cochain / truncation
    / operad / resolution) are *definitionally* equal to
    `canonicalGradeMap`, so pairwise agreement theorems are `rfl`.
    Headline theorem `truncation_operad_grade_agree` proves the
    HoTT ↔ Higher Algebra Lens-level equation — they project to
    the same Raw-level kernel, hence are one Reading under
    different vocabularies.  Carrier-level `*_realize_a` /
    `_b` theorems show that the enriched `Raw.fold` (e.g.,
    `Raw.fold EdgeWalk.two EdgeWalk.three EdgeWalk.concat`)
    projects to the canonical value on atoms.

Avoids `HasDistinguishing`-typeclass plumbing (which would bring
`propext`); the literal Nat-level `Raw.fold 2 3 (· + ·)` with
`Nat.add_comm` discharging `Raw.fold_slash`'s combine-symmetry
hypothesis is PURE.

Tracking:
  · `lake build E213.Lib.Math.GRA` — 49/49 modules clean.
  · `tools/scan_axioms.py` — 296 PURE / 0 DIRTY (with 13
    additional HigherAlgebra decls verified PURE via direct
    `#print axioms`).

## Previous step — Phases 12–15 (259 PURE / 0 DIRTY)

7 new files extending GRA from 14 → 21 files, 167 → 259 PURE:

  · **Phase 12 (4 files)** — full carrier enrichment for the
    remaining 4 Readings (R₁/R₂/R₃/R₅), each parallel to
    `WalkEnrichment` (R₄):
      · `CochainEnrichment.lean` (12 PURE) — `Cochain` with
        degree constraint; cup-product `cup` and `tensor`;
        `GRA23_CochainEnriched` instance + `forgetHom`.
      · `HoTTEnrichment.lean` (12 PURE) — `Truncation`
        carrying homotopy level; suspension `Σⁿ` and smash `∧`;
        `GRA23_TruncationEnriched` + `forgetHom`.
      · `HigherAlgebraEnrichment.lean` (12 PURE) — `Operad`
        carrying `E_n` level; Day convolution + nested
        integration; `GRA23_OperadEnriched` + `forgetHom`.
      · `AnalysisEnrichment.lean` (12 PURE) — `Resolution`
        carrying analytic exponent; modulus composition +
        polynomial-depth product; `GRA23_ResolutionEnriched`
        + `forgetHom`.
  · **Phase 13 `Naturality.lean`** (13 PURE) — translation
    between enrichments is natural with respect to the
    forgetfuls.  Per-Reading `*_depth_natural` theorems +
    `DepthNaturality` capstone bundle.  `walk_cochain_*`
    theorems show cross-Reading translation via the hub.
  · **Phase 14 `SectionRetraction.lean`** (17 PURE) — each
    forgetful has a `Nat → Enriched` section on the valid
    image (`n = 0 ∨ n ≥ 2`).  `forget ∘ section = id`
    (retraction) and `section ∘ forget = id` (section
    identity) for all 5 enrichments.  `WalkRetract` packages
    the data.
  · **Phase 15 `Monoidal.lean`** (14 PURE) — `product :
    GRAModel → GRAModel → GRAModel` is the (2, 3)-monoidal
    product with component-wise `⊕`/`⊗` and additive grade.
    `trivial23` is the unit (one-element carrier, grade ≡ 0).
    `leftUnitHom`/`rightUnitHom` are the unit `GRAHom`s.

Tracking:
  · `lake build E213.Lib.Math.GRA` — 27/27 modules clean.
  · `tools/scan_axioms.py` — 259 PURE / 0 DIRTY total (with
    13 additional HigherAlgebra decls mis-attributed by the
    scanner's last-namespace heuristic but verified PURE by
    direct `#print axioms`).

## Previous step — Phases 7–11: category + enrichment (167 PURE)

5 new files extending GRA beyond the original Marathon 16 closure:

  · **Phase 7 `Category.lean`** (9 PURE) — 213-native
    universe-polymorphic `Cat` typeclass; `GRACat` for all GRA
    models; `Reading` enumeration of the 6 closed (2,3)-models;
    `ReadingCat` sub-category; `ReadingCat_connected` witness
    that every pair of Readings is related by a hub-and-spoke iso.
  · **Phase 8 `Groupoid.lean`** (10 PURE) — `Groupoid` typeclass
    sitting on top of `Cat`; pointwise `HEq`-form of "every
    `Reading.iso r s` is the identity at the carrier level" (the
    `HEq` form is forced because abstract `r.toModel.Carrier` and
    `s.toModel.Carrier` are syntactically distinct even though
    both reduce to `Nat`); `ConnectedHub` structure with
    `Reading.hubAtNT` as the concrete hub-and-spoke witness.
  · **Phase 9 `Hom.lean`** (10 PURE) — `GRAHom` (general
    structure-preserving map, not necessarily invertible);
    `id`/`comp` category laws; forgetful `GRAIso → GRAHom`
    (`isoToHom`) functoriality (refl/trans preservation);
    grade-agreement (`GRAHom.grade_agree`) and
    grade-oplus-via-hom (`GRAHom.grade_oplus_via`).
  · **Phase 10 `DepthFunctor.lean`** (9 PURE) — `GRA23` structure
    packaging the (2, 3)-parameter constraint; `GRA23.depth_const`
    showing all (2, 3)-models agree on depth; `readingToGRA23`
    upgrading each `Reading` enum to `GRA23`;
    `Reading_depth_const` as the capstone "depth is the unique
    structural invariant" claim.
  · **Phase 11 `WalkEnrichment.lean`** (12 PURE) — concrete
    carrier enrichment for R₄: `EdgeWalk` with
    `length = 0 ∨ length ≥ 2` bipartite constraint;
    `concat`/`tensor` operations; `GRA23_EdgeWalk` instance;
    `forgetHom` exhibiting the simplified `GRA23_Graph` as the
    image of `EdgeWalk` under the forgetful functor.

Total **167 PURE / 0 DIRTY** across all 14 files of `Lib/Math/GRA/`.

## Previous step — GRA full clear (Marathon 16 → 118 PURE / 0 DIRTY)

  · **Tier 5.1 cleared**: all `Lib/Math/GRA/` theorems are now
    STRICT ∅-axiom PURE.  Pattern:
      · switch `GRAModel.ax_coprime` from `Nat.gcd` (DIRTY via
        well-founded recursion) to `gcd213` (kernel-reducible)
      · introduce `GRA/Common.lean` with shared PURE Nat lemmas
        (`coprime_2_3`, `reach_23`, `depth_formula`, `ceil3_le_ceil2`,
        + `div3_3k_{1,2,3,4}` building blocks)
      · per-Reading proofs collapse to `rfl` / `Nat.le.refl` /
        delegation to Common
      · Translation theorems use Common helpers + explicit
        `Nat.add_le_add_left` / `Meta.Nat.NatDiv213.div_mul_le_self`
        / `Meta.Nat.AddMod213.div_add_mod` chains
      · No `omega`, no `simp [...]`, no Mathlib, no `Classical`.
  · Updated `STRICT_ZERO_AXIOM.md` Tier 5.1 from "backlog" to
    "CLEARED" with the upgrade pattern catalog.
  · Updated `theory/math/gra_book.md` + `graded_residue_arithmetic.md`
    + GRA umbrella docstring + `theory/math/graded_residue_arithmetic.md`
    file listing to reflect PURE status and add `Common.lean`.

### Math umbrella fixes (separate, prior commit)

7 pre-existing build failures in `Lib/Math` fixed:
`Extras` (unterminated docstring), `DyadicFSM/Pell/ProperMod`
(missing `ArithFSM` open), `ParadigmDomainGradedRing`
(`binom_5_row_sum` → `binom_5_row` rename), `ModArith/JoinEquivGCD`
(orphan `(gcd213_self ...)` fragments + missing `succ_sub_self_213`
in open), `AngleStructure/RotationOrder` (re-added
`angle_level{0,1,2}` projections), `CayleyDickson/Levels/Cayley`
(misplaced `open Cayley`), `Cauchy/Wallis` (orphan partial open).
Full `lake build` now 985/985 clean.

## Previous step — GRA promotion + essay (same session)

  · **Promotion**:
      · Created umbrella `lean/E213/Lib/Math/GRA.lean` and wired it
        into `lean/E213/Lib/Math.lean`.
      · Fixed pre-existing build failures in Marathon 16 code
        (omega could not bridge `(n+2)/3` vs `n/3 + (if n%3=0 then
        0 else 1)` without case-splitting on `n % 3 = 0`; affected
        6 files: `NumberTheory`, `Graph`, `Analysis`, `Cohomology`,
        `HoTT`, `HigherAlgebra`, `Translation`).
      · Added `hgen1`/`hgen2` hypotheses to
        `Translation.transport_depth_bound` (lemma was under-
        determined without gen2 equality).
      · Fixed simp-collapse on `master_translation*` (P((n+2)/3)
        repeated collapses to single P-application via and_self).
      · Marked `theory/math/gra_book.md` + `theory/math/graded_
        residue_arithmetic.md` as **CLOSED** (Marathon 16).
      · Added GRA entry to `lean/E213/ARCHITECTURE.md` Lib/Math/.
      · Added Tier 5.1 backlog entry to `STRICT_ZERO_AXIOM.md`
        for `Lib/Math/GRA/`'s ~67 `[propext, Quot.sound]`
        DIRTY theorems (mechanical omega→decide upgrade path).
      · Archived G148 / G150 / G151 to `research-notes/archive/`.
  · **Essay**: `theory/essays/gra_universality_one_principle.md`
    — "Walk-length, cup-length, truncation, chromatic height,
    resolution exponent — why are these the same?"  Derives
    answer via the `GRA23_*` instances + the master translation
    + the universal depth comparison; cross-frame with det(P)=1
    + Frobenius=1 + K_{3,2}^{(c=2)} closure form; honest open
    frontier (carrier-enrichment Phase 7).

## Previous session — GRA Universality Phase 6 COMPLETE (MARATHON DONE)

### Phase 6: Translation Theorems (ALL DONE)

  · `Translation.lean` — 9 sections, ~250 lines, 0 sorry
  · **T1 (R₄→R₁)**: `graph_distance_implies_cup_length`
    Walk-length depth = cup-length depth (identical formulas)
  · **T2 (R₅→R₃)**: `resolution_depth_implies_cell_count`
    Modulus composition depth = homotopy cell-count
  · **T3 (R₁→R₅)**: `cup_grade_is_resolution_compose`
    Cup-grade sum = resolution shift composition
  · **T4 (Prediction)**: `universal_depth_comparison`
    ⌈n/3⌉ ≤ (n+1)/2 — greedy on gen2 always beats naive gen1
    Novel result valid simultaneously in all 5 Readings
  · **Master Translation**: `master_translation_from_any`
    Any P((n+2)/3) implies P holds for all 5 depth functions
  · **Capstone**: `GRA_TranslationProgramme` + `gra_translation_witness`
    All translation results bundled

### Previous session — Phases 1–5

  · `GRAModel.lean`: typeclass + GRAIso refl/symm/trans
  · 5 Reading instances: NT, Graph, Analysis, Cohomology, HoTT, HigherAlgebra
  · `GRA_Universality` + `gra_universality_witness`: all pairwise iso
  · Hub-and-spoke architecture (NT hub, transitivity for all pairs)

## ★ GRA MARATHON STATUS: COMPLETE ★

All 6 phases of the GRA Universality marathon (Blueprint 16) are done:
- 8 Lean files, ~850 lines total
- 0 sorry, 0 native_decide, 0 external axioms, 0 Mathlib
- Typeclass + 5 instances + 5 isos + universality capstone + translations
- Blueprint success criteria met:
  ✓ GRAModel typeclass: 0 sorry, ∅-axiom
  ✓ 5 instances (NT, Graph, Analysis, Cohomology, HoTT, HigherAlgebra)
  ✓ 5 iso proofs (each Reading ≅ NT)
  ✓ Transitivity capstone
  ✓ ≥1 translation theorem (multiple, including novel prediction)

## Tier summary (cumulative)

| Tier | Programme | Status |
|------|-----------|--------|
| 1.1 | Per-layer ψ-kernel completeness | CLOSED |
| 1.2 | Arity c=2 Lean theorem | CLOSED |
| 1.3 | Pell-orbit Stern-Brocot extension | CLOSED (4/4) |
| 1.4 | α_em Step 5 purity | CLOSED |
| 2.1 | Hodge ↔ universe-chain | CLOSED |
| 2.2 | Cayley-Dickson ↔ Möbius | CLOSED |
| 2.3 | p-adic ↔ Möbius P mod-p | CLOSED |
| 3.2 | PRIMARY cup-image boundary framing | CLOSED |
| 4.1 | Catalog ↔ Lean parity | CLOSED |
| 5.2 | Universal P^n entry formula | CLOSED |
| 5.3 | Fibonacci Cassini from P^n det | CLOSED |
| 5.4 | Convergent det / Farey property | CLOSED |
| 5.5 | G139 self-form (iteration + uniqueness) | CLOSED |
| **16** | **GRA Universality (Phases 1–22)** | **★ CLOSED + PROMOTED + 401 PURE ★** |

## Genuinely open (next session targets)

  · **GRA carrier enrichment**: lift from Nat to Walk/Cochain/etc.
    (enrichment is beyond blueprint scope — optional Phase 7)
  · **Tier 3.1**: depth-3 cohomology (c = 3 extension)
  · **Tier 4.2**: Hadron baryon spectrum (channel-sum deployment)
  · **Tier 5.1**: propext unsealing (~20 DIRTY → PURE)
  · **G138 Pattern A**: Modulus-functor 4-way extension
  · **G138 Pattern F**: Multiplicity doctrine chapter
  · **CrossAddress → Functor**: triple-axis schema elevation
  · **New marathon candidate**: next blueprint from `blueprints/`

## Boot order

  · `seed/AXIOM/05_no_exterior.md` §5, §8.4
  · `theory/lens/unified_equivalence.md`
  · `theory/INDEX.md`
  · `lean/E213/ARCHITECTURE.md`
  · `theory/PROMOTION_CRITERIA.md`
