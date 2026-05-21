# Recursor Inventory

CAT-3 per `research-notes/G107_action_items_registry.md` §10.2.

Distilled from G105 §2 (`research-notes/G105_namespace_shape_and_full_recursor_inventory.md`).

The full inductive-type recursor census across `lean/E213/`:
**185 distinct inductive types** with recursor invocations,
totalling tens of thousands of Expr-level edges.

## Method

Re-scan `_ast_callgraph_edges.tsv` (G102) for all callees ending
in `.rec` / `.recAux` / `.recOn` / `.brecOn` / `.casesOn`.
Group by inductive type, count total invocations + distinct
callers.

## Top-12 by total invocation count

| Rank | Total | Inductive type | Recursors (count/callers) | Role |
|-----:|------:|----------------|---------------------------|------|
| 1 | 1,681 | `Bool` | `casesOn` (1681/634) | Boolean case-splits on decide outputs |
| 2 |   803 | `Nat` | `brecOn` (152/152), `casesOn` (501/325), `recAux` (150/150) | Arithmetic induction + cases |
| 3 |   572 | `Eq` | `rec` (248/111), `casesOn` (324/138) | Dominant elaborated rewriting mechanism |
| 4 |   562 | `Decidable` | `casesOn` (562/214) | Direct case-split on Decidable instances (Pattern #2-adjacent) |
| 5 |   377 | `And` | `casesOn` (377/180) | Conjunction destructuring |
| 6 |   285 | `Exists` | `casesOn` (285/150) | Existential destructuring |
| 7 |   284 | `Or` | `casesOn` (284/119) | Disjunction destructuring |
| 8 |   256 | `Prod` | `casesOn` (256/225) | Pair destructuring |
| 9 |   154 | `List` | `casesOn` (114/94), `brecOn` (38/38), `rec` (2/2) | List induction |
| **10** | **104** | **`E213.Term.Internal.Tree`** | **`casesOn` (64/46), `rec` (25/25), `brecOn` (15/15)** | **The Raw-substrate Tree recursor — the SINGLE E213-internal entry in the top 11.** |
| 11 |    65 | `EStateM.Result` | `casesOn` (65/22) | Metaprogramming plumbing |
| 12 |    57 | `Ordering` | `casesOn` (57/53) | Comparator case-split |

## What G90's earlier scan missed

G90 (`tools/ast_fold_scan_body.lean`) had a hardcoded recursor
list of 5 names (`List.foldl/foldr/rec`, `Nat.recAux/brecOn`)
yielding 720 sites.  This understated the true recursor
landscape by **~50×**:

  · **`Bool.casesOn`** at 1,681 invocations is the single largest
    recursor — G90 missed it because the name shape is `casesOn`,
    not `.rec` / `.foldl`.
  · **`Decidable.casesOn`** at 562 invocations.
  · **Connective `casesOn`** (And/Or/Exists/Prod) at 1,202
    combined — the destructuring backbone of DRLT proofs.
  · **`Eq.rec` + `Eq.casesOn`** at 572 combined — elaborated form
    of `rw` / `▸` rewriting.
  · **`E213.Term.Internal.Tree` recursors** at 104 invocations —
    the Expr-layer signature of the 23 `a | b | slash`
    declarations in G94 §6.

## Architecturally significant findings

  · **Only one E213-internal inductive in the top 11**:
    `E213.Term.Internal.Tree`.  All other heavy-use recursors
    are Lean-core inductive types.  Consistent with the
    Reading (γ) finding (`seed/RAW_DERIVATION_SPEC.md`): DRLT's
    Expr-level substrate is overwhelmingly Lean-stdlib generics,
    with the Tree recursor as the Raw-side touchpoint.
  · **Bool dominates** (1,681) because most DRLT theorems
    eventually case-split on a `decide` output via `Bool.casesOn`.
    This is the Pattern #2 operational signature at the recursor
    layer.
  · Combined connective destructuring (And/Or/Exists/Prod) is
    ~1,200 — proof-by-cases is the most common compound proof
    style.

## Regenerating

```
python3 tools/ast_callgraph_scan.py
# produces _ast_callgraph_edges.tsv

awk -F'\t' '$2 ~ /\.(rec|recAux|recOn|brecOn|casesOn)$/ \
  { gsub(/\.(rec|recAux|recOn|brecOn|casesOn)$/, "", $2); print $2 }' \
  _ast_callgraph_edges.tsv | sort | uniq -c | sort -rn | head -50
```

Or re-derive from G102's atlas TSV.

## Cross-references

  · `research-notes/G105_namespace_shape_and_full_recursor_inventory.md`
    §2 — full data + per-type breakdown.
  · `research-notes/G90_ast_fold_motifs.md` — earlier 5-recursor
    pass (corrected by G105).
  · `seed/RAW_DERIVATION_SPEC.md` — α/β/γ context for the
    Lean-stdlib substrate finding.
