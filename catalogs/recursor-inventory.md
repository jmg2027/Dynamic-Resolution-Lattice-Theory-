# DRLT Recursor Inventory (G105 §2)

Complete inventory of inductive types whose recursors are
invoked across DRLT's elaborated proof terms.  Derived from
`tools/_ast_callgraph_edges.tsv` (G102) by filtering callees
ending in `.rec` / `.recAux` / `.recOn` / `.brecOn` /
`.casesOn`.

**185 distinct inductive types** use recursors.  Corrects G90's
hardcoded 5-tag inventory (an artifact of pattern-list
limitation, not a true narrowness).

Source: `research-notes/G105_namespace_shape_and_full_recursor_inventory.md` §2.

---

## Top 12 inductive types by recursor invocation count

| Total | Inductive | Recursors used (count/callers) |
|------:|-----------|---------------------------------|
| 1,681 | `Bool` | `casesOn` (1681 / 634) |
| 803   | `Nat`  | `brecOn` (152/152), `casesOn` (501/325), `recAux` (150/150) |
| 572   | `Eq`   | `rec` (248/111), `casesOn` (324/138) |
| 562   | `Decidable` | `casesOn` (562/214) |
| 377   | `And`  | `casesOn` (377/180) |
| 285   | `Exists` | `casesOn` (285/150) |
| 284   | `Or`   | `casesOn` (284/119) |
| 256   | `Prod` | `casesOn` (256/225) |
| 154   | `List` | `casesOn` (114/94), `brecOn` (38/38), `rec` (2/2) |
| **104** | **`E213.Term.Internal.Tree`** | **`casesOn` (64/46), `rec` (25/25), `brecOn` (15/15)** |
| 65    | `EStateM.Result` | `casesOn` (65/22) |
| 57    | `Ordering` | `casesOn` (57/53) |

The top 12 carry ~70 % of all recursor invocations.  Notable:
**`Tree`** (E213-internal) is the only E213 entry in the top 12.

---

## Reading

  · **Bool.casesOn dominates** (largest single recursor at
    1,681 invocations across 634 callers).  Boolean case-splits
    on decide outputs.  Confirms Pattern #2's footprint at the
    recursor level.
  · **Nat recursors** distributed: brecOn (well-founded), recAux
    (structural), casesOn (case-split) — three flavours covering
    different recursion shapes.
  · **Eq + Decidable + connectives** (And/Or/Exists/Prod):
    1,764 invocations.  Standard constructive-logic destructuring.
  · **Tree** at 86 callers — DRLT-unique structural-induction
    signature on the Raw atomic 4-clause carrier.

---

## E213-internal inductive recursors (after Tree)

Cohomology / Lib infrastructure inductives:

| Total | Inductive | Notes |
|------:|-----------|-------|
| 53 | `Cohomology.Surfaces.T2Squared.Cell2` | T²×T² cell |
| 52 | `Lens.Number.Nat213.Peano.Nat213` | DRLT's own Nat encoding |
| 46 | `Theory.Raw`                | Raw's own .rec (only) |
| 35 | `PatternCatalog.Algebra.OpWord` | Operation word |
| 27 | `CascadeCalculus.Core.Status` | Cascade status |
| 23 | `SyntacticInternalization.Glyph` | Syntactic glyph |
| 20 | `ArityForcingGeneral.RawNk` | Raw N-k variant |
| 17 | `Meta.AxiomMinimality.TreeA` | TreeA variant |
| 17 | `Cohomology.Surfaces.T2Squared.Cell1` | T²×T² cell |
| 17 | `Cohomology.Surfaces.T2Minimal.Cell1` | T² cell |
| 17 | `Meta.AxiomMinimality.NoA.TreeB` | TreeB variant |
| 16 | `Term.Term` | Term-level abstraction |
| 13 | `Cohomology.Surfaces.P1Squared.Cell2` | ℙ¹×ℙ¹ cell |
| 12 | `Meta.AxiomMinimality.NoDistinct.TreeFree` | TreeFree variant |
| 11 | `Cohomology.Surfaces.T2Squared.Cell3` | T²×T² cell |
| 11 | `Choice.BootstrapWitness.StructurallyNat` | Structural Nat |
| 11 | `Theory.Atomicity.ArityForcing.Raw3` | Raw 3-arity variant |
| 10 | `Real213.Sum.Signed.SignedCut` | Signed cut |
| 10 | `Lens.Lens` | Lens type |
|  9 | `PatternCatalog.Algebra.Primitive` | Primitive |
|  9 | `Lib/Math/CayleyDickson/Integer/ZI.ZI` | Gaussian integer |
|  9 | `Lib/Math/Probability/Bridge/Bayesian/BetaCount` | Beta count |
|  9 | `Lib/Math/Analysis/FluxMVT/FluxCut.FluxCut` | Flux cut |
|  9 | `Lib/Math/CayleyDickson/Integer/ZSqrt.ZSqrt` | √D ring |

Notable E213-internal recursors include:
  · **Tree variants** (RawCmpIndependence Tree variants for
    axiom-minimality study, AxiomMinimality TreeA/TreeB/TreeFree)
  · **Surface cells** (T2Minimal/T2Squared/P1Squared/P2Minimal
    Cell0-Cell3) — Cohomology Surfaces CW model recursors
  · **Algebra carriers** (ZI, ZSqrt, ZOmega, ...) — CayleyDickson
    integer ring recursors
  · **Pattern infrastructure** (OpWord, Status, Glyph, RawNk) —
    Tier-1 pattern catalog inductives

---

## Recursor naming convention

  · `.rec` — basic recursor (motive + per-constructor cases)
  · `.recAux` — auxiliary recursor (elaborator-generated)
  · `.recOn` — recursor with target as first explicit arg
  · `.brecOn` — bounded recursion (well-founded)
  · `.casesOn` — case-split without recursive call

`recAux` + `brecOn` are Lean elaborator artifacts of `match`
expressions over recursive types.  `rec` is the principle-of-
induction form.  `casesOn` is the non-recursive case-split.

---

## How to refresh this catalog

Re-run scan + analysis:
```
python3 tools/ast_callgraph_scan.py        # regenerates edges TSV
python3 -c "..."                            # filter callees ending
                                            # in .rec/.recAux/.recOn/.brecOn/.casesOn
                                            # then group by inductive prefix
```

Inline script in `G105_namespace_shape_and_full_recursor_inventory.md`
§2 produces this catalog.

---

## Cross-references

  · `research-notes/G90_ast_fold_motifs.md` — original (incomplete)
    fold/recursor scanner.  G90 hardcoded 5 tags
    (List.foldl/foldr/rec, Nat.recAux/brecOn) — produced the
    "narrow recursor vocabulary" claim that G105 §2 corrects.
  · `research-notes/G105_namespace_shape_and_full_recursor_inventory.md`
    — full inventory with correction.
  · `research-notes/G111_cohomology_deep_dive.md` §3 — Tree
    recursor usage in Cohomology.
  · `LESSONS_LEARNED.md` Pattern #13 — decide-finitism
    quantitative profile.
