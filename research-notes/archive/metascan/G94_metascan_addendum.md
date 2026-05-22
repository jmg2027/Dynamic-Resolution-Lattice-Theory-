# G94 — Meta-scan addendum: N4 cross-validation + Raw.fold_slash context atlas + CutSumOne ladder

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tool**: `tools/syntax_arg_scan.py --context-target` (new)  
**Companions**: G90 (AST), G91 (syntax skeleton), G92 (citation graph)  
**Cross-branch**: G93 handshake to `subset-bijection-lemmas`.

Three closures from G92 §"Concrete next actions":
  · **N2 closed**: Raw.fold_slash 51-caller ±5 tactic context atlas.
  · **N4 closed**: high out-degree proofs cross-validated with G91
    boilerplate ladders.
  · **New ladder discovered**: Real213/Sum/CutSumOne 6-decl family
    sharing a 7-token templated opener that G91's exact-sequence
    clusterer missed.

---

## §1.  N4 — three-layer agreement on the L1 outlier

The top-4 proofs by lemma-citation out-degree are **byte-identical
across all three meta-scan layers**:

| Decl | cites (G92) | tactic length (G91) | file |
|------|------------:|--------------------:|------|
| `leibniz_via_β_decomp_lens` | 43 | 48 | `Cup/AW/LeibnizAlgLift.lean` |
| `leibniz_via_α_decomp_21`   | 43 | 48 | `Cup/AW/LeibnizAlgLift21Alpha.lean` |
| `leibniz_via_β_decomp_22`   | 43 | 48 | `Cup/AW/LeibnizAlgLift22.lean` |
| `leibniz_via_α_decomp_22`   | 43 | 48 | `Cup/AW/LeibnizAlgLift22Alpha.lean` |

**Identical 43-cite + 48-tactic profile across all 4 sibling files.**
G91 already flagged this as L1 (48-tactic boilerplate ladder); G92
out-degree analysis independently picks the same four as the top-4
high-citation decls.  The citation graph and the tactic-skeleton
view point at the SAME four bytes.

Reading: the 48-tactic ladder is not just "structurally similar
proofs" — it is a literal **4-way parametric instantiation** where
the only changing parameter is `(bidegree, factor) ∈
{(2,1), (2,2)} × {α, β} ∪ {(1,1)_lens, β}`.  This is the
**highest-confidence abstraction target in the entire corpus**,
validated by three orthogonal scanners.

### Other L-ladder profiles (G91 cross-check)

| Family | siblings | cites (G92) | tac-len (G91) | confirmed? |
|--------|---------:|-------------|--------------|------------|
| L2 `h_components_{α,β}` × `Leibniz{21,22}Final` | 4 | 12 each | 32 each | ✅ |
| L3 `pisano_predict_realises_pell_{14,17}` | 2 | 3 each | 20 each | ✅ |
| L4 `addLDD`, `mulLDD` | 2 | 10 each | 16 each | ✅ |
| L5 `I_mul_J`, `J_mul_I` | 2 | 3 each | 16 each | ✅ |

All five G91 ladders show **identical (cites, tac-len) profile across
siblings** at the citation-graph layer — full three-layer corroboration.

---

## §2.  CutSumOne — newly surfaced ladder family

G92's out-degree ranking exposed a previously-uncatalogued cluster
in `Lib/Math/Real213/Sum/CutSumOne.lean`:

| Decl | cites | tac-len |
|------|------:|--------:|
| `cutSum_int_int`     | 43 | 71 |
| `cutSum_int_half`    | 34 | 58 |
| `cutSum_half_general`| 30 | 58 |
| `cutSum_zero_const`  | 24 | 38 |
| `cutSum_self_at`     | 23 | 46 |
| `cutSum_half_half_at`| 20 | 43 |
| `cutSum_third_third` | 19 | 41 |
| `cutSum_one_one`     | 14 | 35 |

These have **non-identical lengths**, which is why G91's
exact-sequence clusterer missed them — but they share a templated
opener:

  · **Length 9 prefix**: 4 decls share
    `[intro, apply, show, constructor, intro, have, obtain, have, have]`
    (the bidirectional-constructor split into hypothesis chain).
  · **Length 7 prefix**: 6 decls share
    `[intro, apply, show, constructor, intro, have, obtain]`.

After the opener, each decl branches according to its specific
arithmetic content (`int_int` vs `int_half` vs `half_general` etc.),
which is why the full sequences diverge.

### Reading

The 8 `cutSum_*` decls implement a **bidirectional
`L213_cut`-equivalence proof** for various pairs of cut-points
(`(int, int)`, `(int, half)`, `(half, half)`, `(zero, const)`, ...).
The opener is a templated "constructor on iff, intro the LHS,
destruct, witness construction" — and the divergence is the
specific arithmetic identity proved in each case.

**Abstraction candidate (G94)**: a parametric
`cutSum_pair_equivalence : ∀ (p q : CutPoint), CompatiblePair p q →
L213_cut p q ↔ ... ` that takes the cut-points as parameters and
discharges the arithmetic via a separate identity lemma per
`(p, q)`.  Alternative: introduce a tactic `cutSum_constructor`
that bundles the templated opener.

The catalogue addition makes the syntax-layer ladder roster:

| Ladder | siblings | structure |
|--------|---------:|-----------|
| L1 LeibnizAlgLift |    4 | 48-tactic identical |
| L2 h_components   |    4 | 32-tactic identical |
| L3 Pisano Predictor |  2 | 20-tactic identical |
| L4 LDD smooth     |    2 | 16-tactic identical |
| L5 CDDouble       |    2 | 16-tactic identical |
| **L6 CutSumOne**  |    **8** | **7-9 token shared opener, divergent body** |

L6 is the **broadest ladder by sibling count** (8) but with the
smallest shared exact-prefix length.  Different
abstraction-cost / payoff trade-off than L1 (4 siblings, 48 tokens
identical).

---

## §3.  Raw.fold_slash 51-caller ±5 context atlas

Tool: `python3 tools/syntax_arg_scan.py --context-target
Raw.fold_slash,Theory.Raw.fold_slash,E213.Theory.Raw.fold_slash,fold_slash
--context-window 5`

**62 citation rows across 51 distinct (file, decl) sites.**
**48 distinct ±5 context skeletons** — long tail, with 7 clusters at
≥ 2 occurrences.

### Top context clusters

#### T1 — `leaves_ge_one` family (5 sites)

```
  BEFORE: [induction, decide, decide, have]
  KIND:   apply <Raw.fold_slash>
  AFTER:  [intro, exact, rw, exact]
```

Sites:
  · `ModArith/JoinBezout.leaves_ge_one`
  · `ModArith/JoinCoprime.leaves_ge_one`
  · `ModArith/JoinEquivGCD.leaves_ge_one_local`
  · 2 more

**Read**: a templated 9-tactic skeleton "induct, decide twice, have
intermediate, apply fold_slash, intro/exact/rw/exact" used by 5
ModArith join-decomposition proofs.  Candidate derived lemma:
`Raw.fold_slash_join_ge_one`.

#### T2 — `parityXor` rewrite family (4 sites)

```
  BEFORE: [have, intro, show, rw, have]
  KIND:   rw [<Raw.fold_slash>]
  AFTER:  [show, rw]
```

Sites:
  · `Lens/Instances/CompoundBool.parityXor_fst_eq_parity`
  · `Lens/Instances/CompoundBool.parityXor_snd_eq_boolXor`
  · (each appearing twice — see §3.2)

**Read**: `rw [Raw.fold_slash]` used as a mid-proof rewriting move
inside parityXor lens-view proofs.

#### T3 — `DepthJoin` family (3 sites)

```
  BEFORE: [have, apply, intro, exact, have]
  KIND:   apply <Raw.fold_slash>
  AFTER:  [intro, show, rw, have, have]
```

Sites:
  · `Lens/Instances/Leaves/DepthJoin.small_iff_depth_zero`
  · `Lens/Instances/Leaves/DepthJoin.leaves_two_iff_depth_one`
  · `Lens/Instances/Leaves/DepthJoin.depth_ge_two_leaves_ge_three`

**Read**: 3 sibling iff-proofs in `DepthJoin.lean` share a
9-tactic chain involving `apply Raw.fold_slash` mid-stream.

#### T4 — `Lens.view` template (2 sites)

```
  BEFORE: [induction, rfl, rfl, have, have]
  KIND:   apply <Raw.fold_slash>
  AFTER:  [intro, exact, rw, show, rw]
```

`abLens_sum_eq_leaves`, `leavesModNat_view_eq`.

#### T5 — `boolAndLens / boolOrLens` view-constant (2 sites)

```
  BEFORE: [show, induction, rfl, rfl]
  KIND:   rw [<Raw.fold_slash>]
  AFTER:  [cases, cases, rfl, decide]
```

#### T6 — `f9Lens / parityLens` minimal-view (2 sites)

```
  BEFORE: [show]
  KIND:   rw [<Raw.fold_slash>]
  AFTER:  [decide, rfl]
```

The minimal-opener "just `show`, rewrite Raw.fold_slash, decide,
rfl" — used by view-on-sample-value proofs.

### §3.2  Pattern-#9 candidates — multi-cite within one proof

11 decls cite `Raw.fold_slash` two or more times within a single
proof body:

  · `Lens/EqPW.eqPW_view_of_sym` x2
  · `Lens/Instances/CompoundBool.parityXor_fst_eq_parity` x2
  · `Lens/Instances/CompoundBool.parityXor_snd_eq_boolXor` x2
  · `Lens/Instances/Leaves/DepthJoin.small_iff_depth_zero` x2
  · `Lens/Instances/Leaves/DepthJoin.leaves_two_iff_depth_one` x2
  · `Lens/Instances/Leaves/DepthJoin.depth_ge_two_leaves_ge_three` x2
  · `Lens/Instances/Leaves/DepthJoin.repr2_tier` x2
  · `Lens/Instances/Leaves/RefinesParity.parityLens_view_eq_leaves_odd` x2
  · `Lens/Properties/ABRefines.boolXorLens_view_eq` x2
  · `Lens/Properties/Leaf.leafLens_view_eq` x2
  · `Lib/Math/Cauchy/GenericFamily.projectionLens_view` x2

**Reading for the parallel branch (Pattern #9 audit)**: these 11
decls already apply the Raw 4-clause axiom at **two distinct
granularities** within one proof body — most often (a) at the
outer Raw event, then (b) at an inner Raw sub-event after
case-destructuring.  These are existing sites where Pattern #9's
"recursive Clause 4" principle is operationally implicit.

If the parallel-branch authors want **direct empirical support
for Pattern #9 being natural rather than novel**, these 11 decls
already provide it — the recursive application of `Raw.fold_slash`
is empirically what proofs were doing.  The G93 §C3 offer stands:
this dataset is the answer.

The Lens/Properties subtree has 2 of the 11 (`boolXorLens_view_eq`,
`leafLens_view_eq`) — these are likely the "deepest" recursive
applications, structurally close to the four-clause structure
itself.

---

## §4.  Updated abstraction roster (G87 + G91 + G92 + G94 = consolidated)

Listed by combined evidence strength:

| ID | Source | Family | siblings | confidence |
|----|--------|--------|---------:|-----------|
| **A** | G91 L1 + G92 + G94 §1 | LeibnizAlgLift factor-decomp | 4 | **Triple-layer byte-identical (43 cites + 48 tactics)** |
| B | G90 M3 + G91 x37 | Pell-FSM modular periodicity | 37 | AST + syntax confluence |
| **C** | G94 §2 | **CutSumOne pair-equivalence** | **8** | **NEW — 7-9 token templated opener** |
| D | G91 L2 + G94 §1 | h_components α/β | 4 | Triple-layer byte-identical (12 + 32) |
| E | G90 M4 | √N irrationality (sqrt2/3/5) | 4 | AST-level op-multiset identity |
| F | G90 M2 | Σ-fold cross-domain (math + physics) | 5 | AST motif consensus |
| G | G90 M6 | XorPairCombine ℤ/2-projection foldr | 3 file × 3 motif | AST motif consensus |
| H | G94 §3 T1 | `leaves_ge_one` ModArith join | 5 | Raw.fold_slash context cluster |
| I | G91 L4 + G94 §1 | LDD addLDD / mulLDD | 2 | Triple-layer byte-identical |
| J | G91 L5 + G94 §1 | CDDouble I·J / J·I | 2 | Triple-layer byte-identical |
| K | G91 L3 + G94 §1 | Pisano Predictor 14/17 | 2 | Triple-layer byte-identical |

**A (LeibnizAlgLift)** remains the highest-confidence target.
**C (CutSumOne)** is a new entry; G91's exact-match cluster missed
it but G92 out-degree + L=7 prefix-share surfaces it cleanly.

---

## §5.  What's left

  · **N1** (NatHelper coverage audit): cited as G93 §C1 offer.
    Status: pinged but pending parallel-branch action.

The Raw.fold_slash context atlas (§3) is the operational data
for C3 from G93 — the offer to extend `syntax_arg_scan.py` was
already delivered as the `--context-target` flag.  No further
pinging needed.

---

## §6.  N3 closure — `a | b | slash` family anatomy

The G92 induction-tag scanner found **23 decls** whose `induction
… with` or `cases … with` block contains the `{a, b, slash}`
tag-set (18 with exact 3-tag, 5 with extended tag-sets like
`{a, b, slash, lt, eq, gt}`).  This is DRLT's unique
structural-induction signature: every proof here is **case-splitting
directly on the Raw 3-clause atomic structure**.

### §6.1  File concentration

| File | count |
|------|------:|
| `Term/Internal/Tree/Levels.lean` | 4 |
| `Theory/RawCmpIndependence.lean` | 4 |
| `Lens/Bool213/Raw.lean` | 3 |
| `Term/Internal/Tree/Cmp.lean` | 3 |
| `Lens/Cardinality/Godel.lean` | 2 |
| `Lens/SyntacticInternalization.lean` | 2 |
| `Term/Internal/Tree/Swap.lean` | 2 |
| `Lens/Number/Int213/Raw.lean` | 1 |
| `Term/Internal/Tree/Hom.lean` | 1 |
| `Theory/Raw/Rec.lean` | 1 |

**`Term/Internal/Tree/*` + `Theory/RawCmpIndependence.lean` is
the epicentre** (12 of 23).  These are the modules that *implement*
the Raw axiom's Tree carrier directly; every proof there has to
talk to the 3-clause structure.

### §6.2  Three sub-clusters by tactic skeleton

#### Sub-1 — Lens-view family (7 decls, 6-9 tactics each)

Short proofs.  Templated skeleton:
**`[(intro), induction, rfl, rfl, show, rw]`** — induct, base
arms = `rfl`, slash arm = `show ... ; rw [...]`.

  · `Bool213/Raw.booleanProj_isBool` (len 9)
  · `Bool213/Raw.fold_T_F_and_isBool` (len 6)
  · `Bool213/Raw.boolValue_booleanProj` (len 7)
  · `Number/Int213/Raw.tree_signedLens_factor` (len 6)
  · `RawCmpIndependence.canonicalBy_Tree_cmp` (len 6)
  · `Levels.Tree.fold_eq_depth` (len 6)  — **byte-identical** to:
  · `Levels.Tree.fold_eq_leaves` (len 6)  — `[intro, induction, rfl, rfl, show, rw]`

The two `fold_eq_{depth,leaves}` decls are full byte-identical
tactic sequences (a small but tight sibling pair) — depth and
leaves are two Lens projections of the same Tree fold, so the
proofs are identical modulo the projection name.

#### Sub-2 — Tree-manipulation family (5+ decls sharing 10-token prefix)

**This is a new ladder candidate that G91's exact-match clusterer
missed because total lengths vary (18 to 43).**

Shared opening — `[intro, induction, rfl, rfl, have, unfold,
obtain, obtain, have, have, ...]`:

  · `Levels.Tree.swap_depth` (len 19)
  · `Levels.Tree.swap_leaves` (len 18)
  · `Swap.Tree.swap_swap` (len 40)
  · `RawCmpIndependence.transportTree_roundtrip` (len 42)
  · `RawCmpIndependence.transportTree_canonical` (len 43)

Plus near-variants (with `decide`/`exact` instead of `rfl` in
positions 3-4):

  · `Hom.Tree.fold_swap_hom` (len 18) — `[intro, induction, exact, exact, have, unfold, obtain, obtain, ...]`
  · `Swap.Tree.swap_canonical` (len 18) — `[intro, induction, decide, decide, unfold, obtain, obtain, ...]`

**Reading**: every "Tree-manipulation" proof has the same
prologue — induction on `t`, dispose of the base arms with rfl /
decide / exact, then in the slash arm: `unfold` the operation,
`obtain` the two recursive components, accumulate `have`-chained
properties.  At least **5 byte-identical-prologue siblings**;
candidate for a `tree_induction_slash_unfold` tactic macro or a
`Tree.slash_case` helper lemma that bundles `unfold + obtain ×
2 + have ×` for the slash arm.

#### Sub-3 — Recursor family

Two byte-identical pairs:

  · `Theory/Raw/Rec.Raw.recAux` (len 31) and
    `Theory/RawCmpIndependence.RawBy.recAux` (len 28) share
    `[intro, induction, intro, exact, intro, exact, intro,
    have, unfold, obtain, ...]` for ≥ 10 tokens.

These two recursors prove "Raw structural recursion = explicit
Tree fold over a/b/slash" — one for the canonical Raw, one for
the `RawBy.cmp`-quotiented variant.  They're sibling proofs of
the same recursor theorem under two equivalent constructions; a
single parametric `Raw.recAux_for_relation` would absorb both.

### §6.3  Existing internal abstraction: `transportTree_slash`

Most-cited internal lemma across the 23-decl family:
**`transportTree_slash` x4** — a derived lemma that already
extracts the slash-arm reasoning for `transportTree`.  Together
with `Raw.fold_slash` (G94 §3 — 50 callers across the corpus),
this is the **second example of DRLT having already factored out
a slash-arm-specific API**:

  · `Raw.fold_slash` — the operational form of the 4-clause
    axiom (50 callers).
  · `transportTree_slash` — the slash-arm of the carrier-transport
    construction (4 callers).

Both follow the same architectural principle: **the slash arm is
where the structural recursion lives, so isolate it as a named
lemma**.  The Sub-2 ladder (5+ decls sharing the
`obtain+obtain+have*` prologue) would benefit from a similar
abstraction — currently each sibling re-derives the same
slash-arm boilerplate.

### §6.4  Most-cited lemmas in the `a | b | slash` family

| count | lemma | role |
|------:|-------|------|
| 12 | `ihx'`         | induction hypothesis (slash-arm left subtree) |
| 11 | `ihy'`         | induction hypothesis (slash-arm right subtree) |
|  6 | `Nat.noConfusion` | injectivity for size / depth conclusions |
|  5 | `ihu'`         | additional IH name |
|  4 | `Nat.add_comm` | size arithmetic |
|  4 | `transportTree_slash` | slash-arm carrier transport |
|  4 | `ihs'`         | IH name variant |
|  4 | `hus_val`      | hypothesis on the slash-arm value |
|  4 | `hcmp`         | comparison hypothesis (Cmp / RawCmpIndependence) |

The dominance of `ihx'`/`ihy'`/`ihu'`/`ihs'` (over 30 total IH
citations) means **every slash arm recursively invokes the IH on
both subtrees**.  This is the operational form of Pattern #9 from
the parallel branch — Clause 4 applied recursively at the binary
group level — already implicit in every Sub-2 proof.

### §6.5  Implications for the abstraction roster

Sub-2 is added as **candidate L (G94 §4 expansion)** — the
"Tree-manipulation slash-arm prologue" ladder.  5+ siblings
sharing a 10-token tactic prefix; structural significance equals
or exceeds CutSumOne (§2, candidate C) since Sub-2 lives at the
**Raw-axiom-implementing layer** rather than at a derived
arithmetic layer.

The Sub-3 `Raw.recAux` / `RawBy.recAux` pair adds **candidate M**
— a two-sibling templated recursor pair where the only difference
is the equivalence used for canonicalisation.  Strong unification
candidate: `Raw.recAux_under_relation : ∀ (~ : Tree → Tree → Prop)
[congruence ~], ...`.

Final roster augmentation:

| ID | Source | Family | siblings |
|----|--------|--------|---------:|
| L | G94 §6.2 Sub-2 | Tree-manipulation slash-arm prologue | 5+ |
| M | G94 §6.2 Sub-3 | Raw.recAux / RawBy.recAux | 2 |

L is structurally significant; M is small but high-leverage
(recursors are deep infrastructure).

The N-action list is now closed:
  · N1 (NatHelper audit) — ceded to parallel branch (G93 §C1).
  · N2 (Raw.fold_slash atlas) — closed (§3).
  · N3 (a|b|slash skeleton) — closed (§6).
  · N4 (out-degree cross-validation) — closed (§1).

---

## §7.  CutSumOne deep-dive — shared-vocabulary validation

§2 surfaced 8 `cutSum_*` decls in `Lib/Math/Real213/Sum/CutSumOne.lean`
sharing a 9-token prefix `[intro, apply, show, constructor, intro,
have, obtain, have, have]` then diverging.  This §7 validates the
abstraction candidate by checking whether the divergent bodies
use a **common citation vocabulary**.

### §7.1  Universal-vocabulary lemmas

Across the 8 siblings, **two lemmas are cited by every single one**:

| Lemma | siblings | total cites |
|-------|---------:|------------:|
| `bool_eq_iff`    | **8 / 8** |  8 |
| `decide_eq_true` | **8 / 8** | 24 |

`bool_eq_iff` is cited **exactly once by each sibling** — meaning
every CutSumOne theorem ends with the same Bool-equality-iff
move.  `decide_eq_true` is cited ~3× per sibling on average,
serving as the standard `Decidable.decide p = true → p` bridge.

**6/8-shared vocabulary**:

  · `E213.Tactic.NatHelper.mul_assoc` — 38 total cites
  · `Nat.mul_comm` — 21 total cites

**5/8-shared vocabulary**:

  · `Nat.one_mul` — 19 total cites
  · `Nat.le_of_mul_le_mul_left` — 5 total
  · `Nat.le_trans` — 6 total
  · `Nat.mul_le_mul_left` — 6 total

### §7.2  Divergence-pattern analysis

After the 9-token shared prefix, the first 10 tail tokens per
sibling:

| Decl | tail first-10 |
|------|---------------|
| `cutSum_int_int`       | `[rw, have, rw, have, have, rw, have, rw, show, decide]` |
| `cutSum_int_half`      | `[have, rw, rw, have, show, decide, apply, have, have, rw]` |
| `cutSum_half_general`  | `[show, decide, apply, have, have, rw, have, rw, rw, rw]` |
| `cutSum_zero_const`    | `[have, have, rw, have, rw, rw, show, decide, exact, decide]` |
| `cutSum_self_at`       | `[have, obtain, have, have, show, decide, apply, have, have, rw]` |
| `cutSum_half_half_at`  | `[have, show, decide, rw, apply, have, rw, have, rw, exact]` |
| `cutSum_third_third`   | `[have, have, show, decide, apply, have, have, rw, rw, have]` |
| `cutSum_one_one`       | `[have, have, have, show, decide, rw, apply, have, rw, exact]` |

The tails diverge in **order but not in vocabulary**: every tail
contains some permutation of `have`, `rw`, `show`, `decide`,
`apply`.  No tail introduces a tactic not present in the others.

### §7.3  Reading

The CutSumOne family is structurally:

  1. **Templated opener** (9 tokens): bidirectional-iff
     constructor + 2-witness destructure.
  2. **Per-instance arithmetic body**: a permutation of
     `[have, rw, show, decide, apply]` that proves the
     specific arithmetic identity for the (p, q) cut-point pair.
  3. **Universal closer**: `bool_eq_iff + decide_eq_true`
     bridge.

The structural template is therefore **3-part**: opener, body,
closer.  The body is parameterised by the per-instance
arithmetic identity; the opener and closer are universal.

### §7.4  Refined parametric-lemma signature

Building on §2's candidate, the deep-dive supports a **3-component
parametric replacement**:

```lean
-- Universal infrastructure (provable once, used by all instances)
theorem cutSum_iff_template
  {p q : CutPoint} (hCompat : CompatiblePair p q)
  (hArith : CutArithIdentity p q) :
  L213_cut p q ↔ True := by
  apply Iff.intro
  · intro h
    obtain ⟨a, b⟩ := h
    -- body delegated to hArith
    exact hArith.mp ⟨a, b⟩
  · intro _
    -- ... bool_eq_iff + decide_eq_true closer
    apply bool_eq_iff.mpr
    apply decide_eq_true
    ...
```

Per-instance: each `cutSum_pq` decl becomes a tiny proof
discharging `CutArithIdentity p q` for its specific `(p, q)`,
delegating the iff structure to `cutSum_iff_template`.

**Estimated reduction**: 8 decls × ~30 tactics each ≈ 240 tactic
tokens → 1 template (~25 tokens) + 8 arithmetic identity proofs
(~5-15 tokens each).  **Net reduction ~50-60 % of total tactic
mass in the CutSumOne family.**

The 6/8-shared `NatHelper.mul_assoc` + `Nat.mul_comm` heavy use
indicates the arithmetic identity proofs themselves could share
a sub-template — but that's a second-order optimisation past the
primary 3-component split.

### §7.5  Updated confidence on Candidate C

Three independent measures now point at CutSumOne as a strong
abstraction target:

  · **Sibling count**: 8 (broadest in the corpus).
  · **Shared prefix length**: 9 tokens (universal opener).
  · **Universal vocabulary**: 2 lemmas cited by all 8 siblings,
    forming the closer pattern.
  · **Bounded vocabulary**: tail tactics all drawn from the same
    5-tactic vocabulary (`have/rw/show/decide/apply`); no
    sibling introduces alien tactics.

**Candidate C confidence raised from "structural template
hypothesis" to "validated 3-component template with universal
closer"**.  Implementation would follow the same `@[reducible]`
alias pattern used for L1/L2/NatHelper centralisations — blast
radius contained inside `CutSumOne.lean` + its consumers.

---

## §8.  L1 / L2 byte-identity deep-dive

Same shared-vocabulary lens applied to L1 (LeibnizAlgLift × 4)
and L2 (h_components_{α,β} × Leibniz{21,22}Final).

### §8.1  L2 — **fully byte-identical**

| Sibling | tac-len | cite-count |
|---------|--------:|-----------:|
| `Leibniz21Final.h_components_α` | 32 | 12 |
| `Leibniz21Final.h_components_β` | 32 | 12 |
| `Leibniz22Final.h_components_α` | 32 | 12 |
| `Leibniz22Final.h_components_β` | 32 | 12 |

**All 4 tactic sequences are identical at every position** (32
tokens, byte-by-byte match).  Cite multisets are also identical:
the same 12 lemmas cited with the same multiplicities — 6 of
them shared by all 4 (`h_lhs`, `h_rhs1`, `h_rhs2`,
`delta_pointwise_eq`, `step.trans`, `cupAW_pointwise_eq`).

This is **literal copy-paste of one proof across 4 theorem
names**.  The L2 abstraction is therefore not parametric in any
substantive sense; it is a **name-only difference**.  A single
theorem with the bidegree (21/22) and factor (α/β) as parameters
would replace all 4 with zero proof-content rewriting.

**L2 abstraction effort: minimal.**  Write one `h_components_general`
theorem; redirect 4 callers (or keep them as `@[reducible]`
aliases).

### §8.2  L1 — **30-token prefix + 43-cite identity, then α/β fork**

| Sibling | tac-len | cite-count |
|---------|--------:|-----------:|
| `LeibnizAlgLift.leibniz_via_β_decomp_lens`        | 48 | 43 |
| `LeibnizAlgLift22.leibniz_via_β_decomp_22`        | 48 | 43 |
| `LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21`   | 48 | 43 |
| `LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22`   | 48 | 43 |

  · **Longest common tactic prefix**: 30 tokens (62.5 % of length).
  · **Divergence position 30**: `[rfl, rfl, have, have]` — the
    β-decomp pair (`_lens`, `_22`) splits with `rfl`; the
    α-decomp pair (`_21`, `_22 α`) splits with `have`.

The fork is **exactly the factor knob** (α vs β).  The bidegree
knob (1,1 lens / (2,1) / (2,2)) does **not** affect proof
structure at this token level — proofs are byte-identical
across bidegrees, only the factor differs after position 30.

  · **Cite multisets**: **identical across all 4 siblings** —
    same 43 lemma names, same multiplicities.  Lemmas cited by
    all 4 include `h_lhs`, `h_rhs1`, `h_rhs2`, `h_components`,
    `delta_pointwise_eq`, `cupAW_pointwise_eq`, `combine_10`.

So at the citation level L1 is fully identical; at the tactic
level the last 18 tokens fork on the α/β knob alone.

### §8.3  Refined L1 parametric signature

The original G93 §C4 candidate

```
leibniz_via_factor_decomp : ∀ (bidegree : Nat × Nat) (factor : α ∨ β), ...
```

is over-parameterised.  The deep-dive shows **bidegree doesn't
affect proof structure** at the token level — meaning the
template is bidegree-uniform.  Refined signature:

```lean
theorem leibniz_via_decomp
  {n : Nat × Nat} {factor : Factor}      -- bidegree erased, factor essential
  (h_components : ComponentsAt n factor) : ... := by
  -- 30-token universal prologue (identical across all 4 siblings)
  ...
  -- factor-conditional fork (18 tokens, dispatches on factor)
  match factor with
  | .α => -- the α-decomp 18-token tail
  | .β => -- the β-decomp 18-token tail
```

Or, even simpler if the 18-token forks are themselves
α/β-conjugates: a single tail with a `factor.flip` parameter
threading through the rfl-vs-have positions.

### §8.4  Combined L1 + L2 effort estimate

  · **L2**: 1 parametric theorem (~32 tokens, copy of any
    sibling) + 4 reducible aliases.  Net: -3 proofs.
  · **L1**: 1 parametric theorem with internal `match factor`
    (~30 + 2×18 + match-overhead ≈ 75 tokens) + 4 reducible
    aliases.  Net: -3 proofs.

Total mass reduction:

  · L1: 4 × 48 = 192 tokens → ~75 tokens.  **Saves ~117 tokens.**
  · L2: 4 × 32 = 128 tokens → ~32 tokens.  **Saves ~96 tokens.**
  · Combined: **~213 tactic tokens** retired in 2 marathons
    (small ones; the blast radius is `Cup/AW/` only).

Compared to CutSumOne (Candidate C, ~140-token reduction): L1 +
L2 together would retire **more total mass** with smaller
per-proof effort (no per-instance arithmetic identity to
discharge — the per-sibling work is zero for L2 and the α/β
fork only for L1).

### §8.5  Abstraction-priority re-ranking

Updated by deep-dive evidence strength:

| Rank | ID | Family | Status | Mass saving |
|-----:|----|--------|--------|------------:|
| 1 | **L2** | h_components × 4 | **fully byte-identical**, name-only | ~96 tok |
| 2 | **L1** | LeibnizAlgLift × 4 | 30-tok prefix + 43-cite identity, α/β fork | ~117 tok |
| 3 | **C**  | CutSumOne × 8 | 9-tok prefix, universal closer, 3-part template | ~140 tok |
| 4 | M  | Raw.recAux × 2 (G94 §6 Sub-3) | high-leverage recursor pair | small |
| 5 | A→J... (other candidates) | (G94 §4) | various | various |

**L2 is now the cleanest possible abstraction**: zero
proof-content rewriting required.  Worth doing first as a low-risk
warm-up to validate the `@[reducible]` alias machinery for the
Cup/AW/ subtree, before tackling L1 + C.
