# DRLT Internal Hubs (G92 surface + G102 Expr layer)

Top load-bearing E213-internal lemmas + types + carriers,
measured by caller-breadth and total invocation count.

Two measurement layers:
  · **Surface (G92)**: explicit citations via `rw [..]`,
    `apply <name>`, `exact <name>`, `simp only [..]`.  Author
    intent.
  · **Expr (G102)**: every `Expr.const` reference in elaborated
    proof terms.  Mechanical dependency including type
    annotations, typeclass infrastructure, recursor invocations.

Source: `research-notes/G92_citation_graph_and_constructs.md`
+ `research-notes/G102_full_expr_callgraph.md`.

---

## Surface-citation hubs (G92, author intent)

### Top E213-internal hubs by surface citations

| Cites | Callers | Lemma |
|------:|--------:|-------|
| 174 | 58 | `E213.Tactic.NatHelper.mul_assoc` |
|  45 | 27 | `E213.Tactic.NatHelper.add_mul` |
|  20 |  6 | `E213.Meta.Int213.mul_comm` |
|  14 |  6 | `E213.Meta.Int213.neg_mul` |
|  13 |  9 | `E213.Meta.Int213.neg_add` |
|  12 | 12 | `E213.Tactic.NatHelper.add_sub_cancel_right` |
|  11 |  5 | `E213.Tactic.NatHelper.mul_mul_mul_comm_213` |
|  11 |  9 | `E213.Meta.Int213.add_comm` |
|  10 |  6 | `E213.Meta.Int213.mul_neg` |
|   7 |  5 | `E213.Term.Internal.Tree.noConfusion` |

### Notable surface hubs (open'd unprefixed)

These appear unprefixed in citations due to `open` declarations:

| Cites | Callers | Lemma (true full name) |
|------:|--------:|------------------------|
| 61 | 50 | `Raw.fold_slash` (= `E213.Theory.Raw.fold_slash`) |
| 84 | 47 | `decide_eq_true` (Lean-core) |
| 57 | 20 | `leavesModNat_view_eq` (= `E213.Lens.Instances.Leaves.ModNat...`) |
| 45 |  5 | `h_components` (local-have name in L1 family) |

`Raw.fold_slash` is the **second-largest internal hub**: 50
distinct callers.  This is the operational form of the 4-clause
Raw axiom — `apply Raw.fold_slash` is the universal "open the
proof" move when Clause 4 needs to be invoked.

### Top external (Lean-core) cited

| Cites | Callers | Lemma |
|------:|--------:|-------|
| 177 | 104 | `absurd` |
| 165 |  90 | `Nat.mul_comm` |
| 149 |  74 | `Nat.add_assoc` |
| 145 |  99 | `Nat.add_comm` |
|  82 |  62 | `Nat.one_mul` |
|  76 |  59 | `Nat.le_trans` |
|  71 |  45 | `Nat.mul_add` |
|  68 |  68 | `ext` |
|  57 |  49 | `Nat.mul_one` |
|  53 |  29 | `if_pos` |

`absurd` at 104 callers — proof-by-contradiction is DRLT's
dominant negation strategy.

---

## Expr-layer hubs (G102, mechanical dependency)

### Top E213-internal hubs by Expr-layer caller-breadth

| Callers | Total invocations | Const |
|--------:|------------------:|-------|
| 1,087 | 19,102 | `E213.Theory.Raw` (type itself) |
| 614   | 24,059 | `E213.Lib.Physics.Simplex.Counts.binom` |
| 436   | 10,512 | `E213.Theory.Raw.a` |
| 393   |  9,876 | `E213.Theory.Raw.b` |
| 390   | 12,776 | `E213.Lens.Lens.view` |
| 387   |  4,972 | `E213.Lib.Math.Real213.Sum.CutSumTest.constCut` |
| 387   |  8,001 | `E213.Lib.Physics.Simplex.Counts.NS` (= 3) |
| 382   |  3,396 | `E213.Theory.Raw.slash` |
| 317   |  2,175 | `E213.Lens.Lens` |
| 311   |  5,697 | `E213.Lib.Physics.Simplex.Counts.NT` (= 2) |
| 301   |  1,287 | `E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket.DyadicBracket` |
| 297   |  8,241 | `E213.Lib.Physics.Simplex.Counts.d` (= 5) |
| 270   | 21,266 | `E213.Term.Internal.Tree` |
| 269   |  8,872 | `E213.Lib.Math.Real213.Mul.CutMul.cutMul` |
| 211   |    333 | `E213.Lens.Lens.mk` |
| 207   |  4,466 | `E213.Theory.instDecidableEqRaw` |
| 193   |    856 | `E213.Lib.Math.Cohomology.Cochain.Core.Cochain` |

### Reading the Expr-layer hubs

**Raw atoms layer**: `Theory.Raw` (type, 1,087 callers) +
`Raw.a` (436) + `Raw.b` (393) + `Raw.slash` (382) +
`instDecidableEqRaw` (207) + `Tree` (270).  Cumulatively:
**every 7th E213 decl directly references a Raw atom in its
Expr body or type signature** — making Raw atoms the deepest
load-bearing layer.

**Lens layer**: `Lens.view` (390) + `Lens.mk` (211) + `Lens`
type (317).  Lens infrastructure is broadly invoked,
co-equal with Raw atoms in caller-breadth.

**Physics atomicity constants**:
  · `NS` (387 callers) = 3 (number of S-vertices)
  · `NT` (311 callers) = 2 (number of T-vertices)
  · `d` (297 callers) = 5 (atomic level)

These constants are referenced by 287-387 distinct decls
each — **systematically threaded through the corpus**, not
localised to physics modules.  Strong empirical evidence that
the (NS, NT, d) = (3, 2, 5) decomposition is corpus-wide
infrastructure, not a "physics-side" addition.

**Cohomology infrastructure**:
  · `Counts.binom` (614 callers) — Pascal binomial coefficient
  · `Cochain.Core.Cochain` (193 callers) — Bool function type
  · `cutMul` (269 callers) — Cut function multiplication

**Hidden hubs** (G102 surfaced beyond G92):
  · `binom` — appeared via type annotations
  · `NS / NT / d` — physics atomicity constants threaded
    structurally
  · `DyadicBracket` — Analysis-side carrier
  · `Counts.constCut` — Real213 cut infrastructure

These hidden hubs are invisible to G92's surface scan because
they're invoked via implicit elaboration, not explicit citation.

---

## Surface vs Expr comparison

| Metric | G92 surface | G102 Expr |
|--------|------------:|----------:|
| Edges | 7,446 | 147,791 (~20× more) |
| Top E213-internal hub | `NatHelper.mul_assoc` (174/58) | `Theory.Raw` (1,087 callers) |
| Visibility: typeclass infrastructure | none | dominant (89 % invocations) |
| Visibility: type-level references | none | full |
| Cost | regex over .lean source | full `lake build` cycle |

The surface graph is the **sociological** view (author intent);
the Expr graph is the **mechanical** view (elaborator's actual
dependency).  Both matter.  Surface surfaces adoption gaps +
copy-paste patterns; Expr surfaces hidden hubs + type-level
threading.

---

## Heavy proof bodies (top 15 by Expr-node count)

| Nodes | Decl |
|------:|------|
| 697,955 | `CayleyDickson.Integer.ZOmega.normSq_mul` (G114) |
| 628,271 | `Cup/AW/LeibnizAlgLift.leibniz_via_β_decomp_lens` (G106 L1) |
| 628,271 | `Cup/AW/LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21` (G106 L1) |
| 628,271 | `Cup/AW/LeibnizAlgLift22.leibniz_via_β_decomp_22` (G106 L1) |
| 628,271 | `Cup/AW/LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22` (G106 L1) |
| 233,014 | `CayleyDickson.Integer.ZOmega.normSq_eq_zero_iff` |
| 226,403 | `DyadicFSM.Pisano.Predictor17.pisano_predict_realises_pell_17` (G113) |
| 160,321 | `Cup/AW/LeibnizAlgLift21.leibniz_via_β_decomp_21` (5th cousin) |
| 124,061 | `DyadicFSM.Pisano.Predictor14.pisano_predict_realises_pell_14` |
| 119,725 | `Real213.Mul.CutMulComm.cutMulInner_eq_true_iff` (G108) |
| 114,353 | `Cohomology.CupAW.Bilinear.cupAW_add_right` |
| 113,393 | `Cohomology.CupAW.Bilinear.cupAW_add_left` |
| 108,265 | `CayleyDickson.Integer.ZOmega.conj_mul` |
| 103,505 | `CayleyDickson.Integer.ZOmega.normSq_nonneg` |
|  94,835 | `HodgeConjecture.Bridge.MLDecoder.ml_decoder_capstone` |

**Two heaviest single clusters**: ZOmega (1.14 M nodes — 6-theorem
algebra) + L1 LeibnizAlgLift (2.5 M nodes — Cup-AW infrastructure).
Together ~3.6 M Expr nodes = ~25 % of the corpus's total Expr mass.

---

## How to refresh this catalog

```
# Surface-cite refresh
python3 tools/syntax_arg_scan.py          # regenerates _syntax_arg_cites.tsv
python3 tools/syntax_arg_scan.py --report-only  # reports top hubs

# Expr-layer refresh
python3 tools/ast_callgraph_scan.py       # regenerates _ast_callgraph_edges.tsv
python3 tools/ast_callgraph_scan.py --report-only

# Expr-mass refresh
python3 tools/ast_shape_scan.py
```

---

## Cross-references

  · `research-notes/G92_citation_graph_and_constructs.md` —
    surface citation layer (Tier-1.5).
  · `research-notes/G102_full_expr_callgraph.md` — Expr layer
    (Tier-2).
  · `research-notes/G103_raw_depth_and_expr_shape.md` — shape +
    Raw-depth.
  · `research-notes/G106_L1_expr_structure_extraction.md` —
    L1 6-layer overdetermined analysis.
  · `catalogs/cross-domain-identifications.md` — CDIs surface
    from hubs cross-namespace co-occurrence.
