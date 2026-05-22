# G103 — Raw-depth BFS + Expr-shape density: 5-layer L1 + encapsulation

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tools**: `tools/ast_shape_body.lean` + `tools/ast_shape_scan.py`
(NEW) + BFS over `tools/_ast_callgraph_edges.tsv` (G102)  
**Context**: user observation (post-G102) — "정량적 증거가 사실상
모두 Raw axiom에서 derived 됐다고 볼 수 있겠네".

---

## §1.  Raw-depth BFS — honest result + encapsulation reading

### Method

Reverse BFS over the G102 call-graph (147,791 edges) from a seed
set of Raw-atom nodes:

```
{Theory.Raw, Theory.Raw.a, Theory.Raw.b, Theory.Raw.slash,
 Theory.instDecidableEqRaw, Term.Internal.Tree, ...}
```

For each E213.* caller, depth = shortest forward-path length
through E213-internal edges to any Raw atom.  Compiler artifacts
filtered (`.mk.injEq`, `.sizeOf_spec`, `.noConfusion`, `_cstage*`,
`_closed_*`, `.match_*`, etc.) plus my own scanner code (`E213.AstCallGraph.*`).

### Result

Post-filter population: **7,485 real E213 callers**.  Raw-depth
distribution:

| depth | decls | comment |
|------:|------:|---------|
|  0    |     5 | Raw atoms themselves |
|  1    |   953 | direct Raw-atom referrers |
|  2    |   133 | 2-hop derivation |
|  3    |    20 | 3-hop |
| ≥ 4   |     0 |  |
|**reach**| **1,111** | **14.8 %** |
|**unreach**| **6,374** | **85.2 %** |

Max depth observed = 3.  **Only 14.8 % of decls reach a Raw atom
within E213-internal edges**.

### Encapsulation reading

The naive interpretation ("only 14.8 % derive from Raw") is
**wrong** — but the data is interesting precisely because it
shows DRLT's **layered architectural encapsulation**.

Inspection of specific unreached nodes:

```
  E213.Lib.Physics.Simplex.Counts.binom   — calls only `binom.match_1` (self-recursion)
  E213.Lib.Physics.Simplex.Counts.NS      — `def NS : Nat := 3`, no E213 callees
  E213.Lib.Math.Cohomology.Cochain        — type definition, no value? body
```

Three observations:

  1. **Type definitions and primitive `def`s** have no proof body
     or only trivially reference Lean-core (`Nat`, `Bool`).  They
     don't transitively reach Raw at the Expr level even though
     they're Raw-derived in the LOGICAL sense (`#print axioms`
     would confirm they import nothing).
  2. **Layered abstractions** like `binom`, `Cochain`, `hodgeStar`
     are operationally autonomous — each layer's proof bodies
     reference its own API, not the bottom-layer Raw atoms.
  3. The 14.8 % figure measures **direct Expr-level Raw
     reference**, NOT logical derivability.

So "everything derives from Raw" is true at two levels:

  · **Logical derivability**: every E213 proof is closed under
    Lean's kernel + the 4-clause Raw axiom set.  Verified by
    `#print axioms` (G95).
  · **Architectural encapsulation**: each layer (Theory → Lens
    → Cohomology / Physics) exposes an API, and downstream
    proofs use the API rather than re-deriving from Raw atoms.

The Expr-BFS measures something else entirely: **how often a
proof's elaborated term still explicitly references the
bottom-most layer**.  That answer is 14.8 % — and the answer
makes sense for a corpus that has invested in API encapsulation.

For a TRUE "every decl ultimately reaches Raw" measure, one
would need to:
  · Walk SIGNATURE-type dependencies (the carrier types), not
    proof-body refs.  E.g., `cutMin_comm : ∀ p q : Cut, ...`
    — `Cut` is defined as `Cut := Raw → ...` (via Lens), so
    the signature contains a transitive Raw reference even
    though the proof body doesn't.
  · This would require a second Lean-meta scanner that walks
    types, not values.

Deferred as future work.  The current BFS is honest about what
it measures; the user's reading needs the encapsulation
qualification.

---

## §2.  Expr-shape density: DRLT's proof-shape fingerprint

NEW scanner `tools/ast_shape_scan.py` walks every E213.* const's
elaborated `Expr` body and counts each `Expr` constructor.

### Population

  · 17,441 E213.* decls with `value?` body.
  · 14,446,697 total Expr nodes.

### Per-constructor distribution

| Constructor | Sum | Mean / decl | Max |
|------------|----:|------------:|----:|
| `app` (function app)      | 7,036,498 | 403 | 348,936 |
| `const` (const ref)       | 5,332,007 | 306 | 299,455 |
| `lit` (literal)           | 1,144,564 |  66 |  91,974 |
| `bvar` (bound var)        |   741,206 |  43 |  37,948 |
| `lam` (lambda)            |    98,617 |   6 |   3,564 |
| `forallE` (∀)             |    50,657 |   3 |   2,270 |
| `sort`                    |    16,102 |   1 |     987 |
| `letE` (local bind)       |    15,333 |   1 |     347 |
| `mdata`                   |     9,211 |   1 |     438 |
| `proj` (structure field)  |     2,502 |   0 |      18 |
| `fvar`, `mvar`            |         0 |   - |       - |

### Reading: DRLT proof-shape signature

**`app + const + lit + bvar` = 99.4 % of all Expr nodes.**

In words: DRLT proofs are overwhelmingly **flat trees of
function-applications-to-constants-and-literals, with bvar
references**.  Almost nothing else.

Specific implications:

  · **`lam + forallE` = 1.04 %** — higher-order binding
    structure is almost absent.  Most proofs are first-order
    term application chains.  Consistent with the `decide`-
    dominant culture: ground term certificates don't need
    binders.
  · **`letE` = 0.1 %** — local definitions essentially absent
    in elaborated bodies.  When proofs use `have ... ` syntactically
    (1,033 `have → have` bigrams from G91), elaboration usually
    inlines these rather than emitting `letE`.
  · **`proj` = 0.017 %** — structure-field access is near-zero
    at Expr level.  DRLT either avoids structure types or
    abstracts projections through named lemmas.
  · **`fvar = mvar = 0`** — as expected for fully elaborated
    terms (free / metavariables only exist during elaboration).

This is a **proof-style fingerprint**: DRLT's elaborated terms
are syntactically minimal — flat application trees with
literal values and constant references.  Higher-order machinery
is delegated to surface tactic syntax (where it's then
elaborated away into ground-term form).

### Constructor-share comparison vs typical Lean code

This is a rough qualitative comparison (no concrete Mathlib
baseline measured here):

  · Mathlib-style code typically has **higher `lam` / `forallE`
    share** because of `simp`-driven proofs (which produce more
    binder structure), heavy use of structures (more `proj`),
    and instance polymorphism (more `proj` and `lam`).
  · DRLT's profile (`lam` 0.7 %, `proj` 0.017 %) is at the
    **decide / rfl extreme** — ground-term certificates with
    minimal binding.

The user's parallel claim — "DRLT is finitist + decide-driven"
— is **directly visible** in this Expr-shape fingerprint.

---

## §3.  Five-layer L1 confirmation (new layer: Expr-node count)

The L1 LeibnizAlgLift 4-sibling family now has agreement at
**FIVE independent measurement layers**:

| # | Layer | Measure | All 4 siblings |
|--:|-------|---------|----------------|
| 1 | G90 AST | recursor-tag profile | identical |
| 2 | G91 syntax | tactic-token count | **48** each |
| 3 | G92 citation | distinct-cite multiset | **43** each |
| 4 | G102 Expr | const-invocation total | **206,914** each |
| 5 | **G103 Expr** | **total Expr-node count** | **628,271** each |

Five-fold byte-identical agreement.  No knob (bidegree, factor)
affects any of these measures.  The four proofs are
operationally one theorem at every layer this branch can
measure.

`LeibnizAlgLift21.leibniz_via_β_decomp_21` (the 5th sibling,
single-factor β at bidegree (2,1)) reaches **160,321 nodes** —
**~25 % of the L1 four** — confirming it's a smaller variant,
not a member of the byte-identical family.

This is the corpus's **maximum-overdetermination signal**.  Any
abstraction-priority weighting that values evidence
concentration places L1 at #1.

---

## §4.  Heaviest proof terms — by node count

Top 15 by total `Expr` node count:

| Nodes | Decl |
|------:|------|
| 697,955 | `ZOmega.normSq_mul` |
| **628,271** | LeibnizAlgLift.leibniz_via_β_decomp_lens |
| **628,271** | LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21 |
| **628,271** | LeibnizAlgLift22.leibniz_via_β_decomp_22 |
| **628,271** | LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22 |
| 233,014 | ZOmega.normSq_eq_zero_iff |
| 226,403 | Pisano.Predictor17.pisano_predict_realises_pell_17 |
| 160,321 | LeibnizAlgLift21.leibniz_via_β_decomp_21 |
| 124,061 | Predictor14.pisano_predict_realises_pell_14 |
| 119,725 | CutMulComm.cutMulInner_eq_true_iff |
| 114,353 | Bilinear.cupAW_add_right |
| 113,393 | Bilinear.cupAW_add_left |
| 108,265 | ZOmega.conj_mul |
| 103,505 | ZOmega.normSq_nonneg |
|  94,835 | MLDecoder.ml_decoder_capstone |

Two clusters dominate:
  · **ZOmega family** — 4 entries (normSq_mul, normSq_eq_zero_iff,
    conj_mul, normSq_nonneg) totaling ~1.14 M nodes.  These
    are the diophantine completeness work (parallel branch
    6-theorem closure).
  · **LeibnizAlgLift family** — 5 entries (the 4 byte-identical
    + LeibnizAlgLift21) totaling ~2.67 M nodes.  L1 cluster
    alone is 2.51 M nodes = ~17 % of the entire E213 Expr
    universe (14.4 M nodes).

A 4-sibling family contributing 17 % of all Expr nodes
(2.51 / 14.4) is the most-concentrated mass in the corpus —
yet another reason L1 is the top abstraction candidate.

---

## §5.  Letter / proj density: heavy local-binding outliers

`letE` heavy callers (excluding compiler artifacts):

| letE | Decl |
|-----:|------|
| 240 | `Bilinear.cupAW_add_right` |
| 240 | `Bilinear.cupAW_add_left` |
| 198 | `AlphaEM.CupChannelInventory.total_edge_cup_channels._cstage*` (artifact-flagged but content non-trivial) |

The two `Bilinear.cupAW_add_*` proofs use 240 `letE` nodes each
— heavy intermediate-value bindings.  This is the cup-product
bilinearity proof, which performs many pointwise computations
with named intermediate cochains.

`proj` is dominated by `instAdd._cstage1` and similar
auto-generated structure-field accessors — none of the proofs
of mathematical interest use proj more than 4-5 times.

---

## §6.  Roster update

After G103:

  · **L1 (LeibnizAlgLift × 4)** stays at **rank #1** under any
    evidence-concentration weighting (5-layer agreement is
    the corpus maximum).
  · **L2 (h_components × 4)** stays at rank #1 under
    abstraction-cost weighting (literal byte-identity).
  · No new abstraction candidates surfaced from G103.

The synthesis G101 + G102 + G103 has now consolidated the
evidence at all measurable layers.  Subsequent work would
either:
  · Execute the surfaced candidates (handover to parallel-style
    work).
  · Extend to NEW layers: signature-type dependency
    (mentioned §1), universe / sort distribution, recursor-by-
    inductive class breakdown.

---

## §7.  Artifacts

  · `tools/ast_shape_body.lean` — Lean Expr-constructor counter
  · `tools/ast_shape_scan.py` — Python driver + reporter
  · `tools/_ast_shape_rows.tsv` — per-decl shape rows
    (gitignored)
  · `tools/_ast_shape_last.log` — last build log (gitignored)

Run: `python3 tools/ast_shape_scan.py` (full pipeline) or
`--report-only` (instant re-cluster).
