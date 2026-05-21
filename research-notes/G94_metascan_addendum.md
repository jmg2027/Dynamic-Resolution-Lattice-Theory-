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

Two more N-actions from G92 remain open:

  · **N1** (NatHelper coverage audit): cited as G93 §C1 offer.
    Status: pinged but pending parallel-branch action.
  · **N3** (a|b|slash 18-decl shared skeleton): unaddressed in this
    addendum.  Tractable — 18 decls is a small set; could be
    closed in a follow-up.

The Raw.fold_slash context atlas (§3) is the operational data
for C3 from G93 — the offer to extend `syntax_arg_scan.py` was
already delivered as the `--context-target` flag.  No further
pinging needed.
