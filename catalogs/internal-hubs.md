# Internal Hubs

CAT-4 per `research-notes/archive/metascan/G107_action_items_registry.md` §10.2.

The load-bearing E213-internal infrastructure across `lean/E213/`.
Use this catalog before any refactor of these names — they have
the largest downstream blast radius.

Sourced from G92 §B
+ G102 §Expr-level.
G102 §2 contains the corrected Expr-level hub list (G104 §3 adds
type-signature hubs).

## Top E213-internal hubs (G92 §B, surface-citation level)

| Lemma | cites | callers |
|-------|------:|--------:|
| `E213.Tactic.NatHelper.mul_assoc` | 174 | 58 |
| `E213.Tactic.NatHelper.add_mul`   |  45 | 27 |
| `E213.Meta.Int213.mul_comm`       |  20 |  6 |
| `E213.Meta.Int213.neg_mul`        |  14 |  6 |
| `E213.Meta.Int213.neg_add`        |  13 |  9 |
| `E213.Tactic.NatHelper.add_sub_cancel_right` | 12 | 12 |
| `E213.Tactic.NatHelper.mul_mul_mul_comm_213` | 11 |  5 |
| `E213.Meta.Int213.add_comm`       |  11 |  9 |
| `E213.Meta.Int213.mul_neg`        |  10 |  6 |
| `E213.Term.Internal.Tree.noConfusion` | 7 |  5 |

**`E213.Tactic.NatHelper.*`** dominates — 5 of top 10 entries.
PURE-replacement layer for `Nat.*` lemmas whose Lean-core forms
import `propext` or `Classical`.  Any change to NatHelper has the
largest blast radius in the corpus.

**Second-tier**: `E213.Meta.Int213.*` — integer-algebra
infrastructure (5 entries).

## Top external + open'd hubs

| Lemma | cites | callers |
|-------|------:|--------:|
| `absurd`        | 177 | 104 |
| `Nat.mul_comm`  | 165 |  90 |
| `Nat.add_assoc` | 149 |  74 |
| `Nat.add_comm`  | 145 |  99 |
| `decide_eq_true`|  84 |  47 |
| `Nat.one_mul`   |  82 |  62 |
| `Nat.le_trans`  |  76 |  59 |
| `Nat.mul_add`   |  71 |  45 |
| `ext`           |  68 |  68 |
| **`Raw.fold_slash`** | **61** | **50** |

`Raw.fold_slash` is E213-internal (shown unprefixed via
`open E213.Theory`).  At 50 distinct callers, it's the
**operational form of the Raw axiom** — anywhere a proof needs to
unfold the 4-clause behaviour, this is the lemma cited.  The
single most-significant internal hub after NatHelper.

## Expr-level hubs (G102, normalised by call graph)

At the Expr layer (Const references in elaborated proof bodies):

| Body callers | Type-sig callers | name |
|-------------:|-----------------:|------|
| 1,087 | 1,183 | `E213.Theory.Raw` |
|   614 |   302 | `Simplex.Counts.binom` |
|   390 |   305 | `E213.Lens.Lens.view` |
|   387 |   322 | `Real213.Sum.CutSumTest.constCut` |
|   317 |   475 | `E213.Lens.Lens` |
|   301 |   308 | `DyadicSearch.DyadicBracket.DyadicBracket` |
|   < 100 |   264 | `Cochain.Core.Cochain` (TYPE-only hub) |

`Cochain.Core.Cochain` is the **type-layer-only hub** — heavily
referenced in signatures (∀ α : Cochain ...) but rarely
instantiated in proof bodies.

`E213.Theory.Raw` is referenced more in **type signatures**
(1,183) than in **bodies** (1,087).  More decls operate on
Raw-typed objects than directly compute via Raw atoms — confirms
the (γ) finding (`seed/THEOREM_METHODOLOGY_SUITE.md` §TH-2): the substrate is
generic-Lean infrastructure, but the types DO carry Raw.

## Centralisation tactics (Pattern #10, this branch)

When a Lean-core hub citation is replaced by an E213-internal
PURE alias (centralisation), the external-hub citation count
drops and the internal-hub count rises.  This branch:

  · `Nat.mul_left_comm` (would-be DIRTY)  →  `NatHelper.mul_left_comm` (PURE), 19 sites.
  · `Nat.add_right_comm` (Lean-core PURE) →  same name, 6 sites (no rename, just adoption).
  · `Nat.max_comm` → `NatHelper.max_comm` (prior branch N5).
  · `Int.mul_sub` / `Int.sub_mul` → `Meta.Int213.{mul_sub, sub_mul}` (prior N6).

After these centralisations, DRLT is **PURE-bounded on Lean 4
core** — no DIRTY-citation chain leaves the kernel.

## Pre-refactor checklist for top hubs

Before renaming / removing any lemma in the top tables:

1. Re-run `tools/ast_callgraph_scan.py` to refresh counts.
2. Confirm all callers continue to build after the change.
3. If renaming, add `@[reducible] def oldName := newName` as an
    alias for downstream consumers.  (Established pattern per
    parallel branch's C1 centralisation work.)
4. Re-run `tools/scan_all_axioms.py` to confirm no DIRTY
    regressions.

## Regenerating

```
python3 tools/syntax_arg_scan.py    # citation counts (G92)
python3 tools/ast_callgraph_scan.py # Expr-level (G102)
python3 tools/ast_typesig_scan.py   # type-signature only (G104)
```

All TSVs are gitignored; scanner code is committed.

## Cross-references

    surface-citation atlas.
    graph.
    type-signature hub asymmetry.
  · `LESSONS_LEARNED.md` Pattern #10 — adoption-gap detection
    methodology that surfaces hub centralisation opportunities.
