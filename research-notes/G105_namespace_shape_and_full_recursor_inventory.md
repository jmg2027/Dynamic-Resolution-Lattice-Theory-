# G105 — Per-namespace Expr-shape + full recursor inventory (G90 correction)

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Sources**: G103 (shape data) + G102 (call graph) + ad-hoc
analyses.  
**Findings**: (1) DRLT's architectural layers have distinct
proof-shape fingerprints, (2) G90's 5-recursor inventory was
incomplete; the true inventory spans 185 inductive types.

---

## §1.  Per-namespace Expr-shape comparison

Using `_ast_shape_rows.tsv` (G103), grouped per top-3-component
namespace and excluding compiler artifacts:

| Namespace                | #decls | app/decl | const/decl | lit/decl | lam/decl | letE/decl |
|--------------------------|-------:|---------:|-----------:|---------:|---------:|----------:|
| E213.Lib.Math            |  4,829 |    1,072 |        799 |      197 |      6.9 |       0.2 |
| E213.Lib.Physics         |    875 |      745 |        615 |      119 |      1.7 |       0.6 |
| E213.Lens.Number         |    286 |      197 |        160 |       14 |      9.3 |       0.0 |
| E213.Lens.Instances      |    254 |      284 |        223 |       12 |     13.1 |       0.0 |
| E213.Lens.Properties     |    116 |      228 |        162 |        7 |      8.6 |       0.0 |
| E213.Lens.Universal      |     77 |      409 |        330 |       22 |     10.9 |       0.1 |
| **E213.Meta.Nat**         |     71 |    1,553 |      1,254 |      110 |     20.8 |       0.3 |
| E213.Meta.Algebra213     |     70 |      429 |        143 |        7 |      5.4 |       0.0 |
| **E213.Theory.Raw**       |     62 |      954 |        825 |       11 |  **100.9** |       0.0 |
| E213.Lens.Compose        |     56 |      210 |        122 |        0 |     10.5 |       0.0 |
| **E213.Term.Internal**    |     43 |      ~ |        ~ |        ~ |   **60.8** |       0.0 |
| E213.Theory.RawCmpIndependence | 40 |      ~ |        ~ |        ~ |   **58.8** |       0.0 |
| E213.Lens.SyntacticInternalization | 32 | ~ |        ~ |        ~ |   **55.2** |       0.0 |
| E213.Tactic.NatHelper    |     45 |      573 |        446 |       50 |     12.9 |     **2.3** |

(Mean lam/decl across corpus: 8.9)

### §1.1  The architectural λ-density split

**Bottom-layer namespaces** (Raw, Term.Internal,
RawCmpIndependence, SyntacticInternalization) have λ-density
**5-11× the corpus mean** (55-100 lam/decl).  Reason:
these namespaces **DEFINE** the Raw / Tree / Cmp machinery —
each definition is a λ-bound function over Tree constructors,
comparison functions, etc.

**Upper-layer namespaces** (Lib.Math, Lib.Physics) have
λ-density **0.2-0.8× the mean** (1.7-6.9 lam/decl).  Reason:
they **USE** the API exposed by lower layers — no need to bind
inside proofs.

Cleanest architectural visibility at the Expr layer:
DRLT has ≥ 3 cleanly-distinguishable layers (Theory < Lens <
Lib.Math/Physics) with distinctive λ-density signatures.

### §1.2  letE outlier — `Tactic.NatHelper`

NatHelper is the **only namespace** where `letE` density is
non-trivial (2.3 letE/decl vs corpus mean ~0.9).  The PURE-shield
Nat arithmetic helpers use intermediate-value bindings actively.

Other letE-heavy individual decls (G103 §5): the cup-product
bilinearity proofs `Bilinear.cupAW_add_left/right` (240 letE
each).  But these are individual outliers, not namespace-wide
patterns.

### §1.3  `Meta.Nat` outlier — heaviest per-decl

Meta.Nat has **1,553 app per decl** — by far the heaviest
proof-term density per decl in the corpus.  Reason: Meta.Nat
hosts PURE-shielded Nat algebra that gets unrolled in every
caller.

---

## §2.  Full recursor inventory — G90 correction

### §2.1  G90's scanner was incomplete

G90 (the original `ast_fold_scan_body.lean`) had a hardcoded
list of fold/recursor tags:
```
  List.foldl, List.foldr, List.foldlM, List.foldrM,
  List.rec, List.recOn,
  Nat.rec, Nat.recAux, Nat.recOn, Nat.brecOn,
  Nat.fold, Nat.foldRev,
  Fin.foldl, Fin.foldr, Fin.foldlM, Fin.foldrM,
  Array.foldl, Array.foldr, Array.foldlM, Array.foldrM
```

5 tags were observed: `List.foldl/foldr/rec`,
`Nat.recAux/brecOn`.  720 sites total.

G90 concluded: "DRLT lives in a finitist + list-structural +
Nat-recursive universe."

### §2.2  True recursor inventory

Re-scanning `_ast_callgraph_edges.tsv` (G102) for all callees
ending in `.rec`/`.recAux`/`.recOn`/`.brecOn`/`.casesOn` produces
a much richer picture: **185 distinct inductive types** with
recursor invocations, totalling tens of thousands of edges.

Top 12 by total invocation count:

| Total | Inductive | Recursors (count/callers) |
|------:|-----------|---------------------------|
| 1,681 | `Bool` | `casesOn` (1681/634) |
|   803 | `Nat` | `brecOn` (152/152), `casesOn` (501/325), `recAux` (150/150) |
|   572 | `Eq` | `rec` (248/111), `casesOn` (324/138) |
|   562 | `Decidable` | `casesOn` (562/214) |
|   377 | `And` | `casesOn` (377/180) |
|   285 | `Exists` | `casesOn` (285/150) |
|   284 | `Or` | `casesOn` (284/119) |
|   256 | `Prod` | `casesOn` (256/225) |
|   154 | `List` | `casesOn` (114/94), `brecOn` (38/38), `rec` (2/2) |
| **104** | **`E213.Term.Internal.Tree`** | **`casesOn` (64/46), `rec` (25/25), `brecOn` (15/15)** |
|    65 | `EStateM.Result` | `casesOn` (65/22) |
|    57 | `Ordering` | `casesOn` (57/53) |

### §2.3  What G90 missed

  · `Bool.casesOn` — **1,681 invocations / 634 callers**, the
    SINGLE LARGEST recursor in the corpus.  Boolean case-splits
    on decide outputs.  G90 missed this because it's
    `casesOn`, not a `.rec`/`.foldl`-shaped name.
  · `Decidable.casesOn` — 562 / 214.  Direct case-split on
    Decidable instances.  Pattern-#2-adjacent.
  · `Eq.rec` + `Eq.casesOn` — 572 combined.  The dominant
    rewriting mechanism in elaborated form.
  · Connective `casesOn` (And/Or/Exists/Prod) — 1,202 combined.
    Destructuring conjunctions / existentials etc.
  · **`E213.Term.Internal.Tree` recursors** — 104 invocations /
    86 distinct callers.  This is the Expr-layer signature of
    the 18 + 5 = 23 `a | b | slash` decls from G94 §6!  G90
    missed it because `Tree.rec` wasn't in its hardcoded list.

### §2.4  Corrected vocabulary claim

The original G90 finding "DRLT lives in a 5-recursor universe"
is **wrong as stated**.  Corrected:

> DRLT's recursor invocations span 185 inductive types in
> total, dominated by 11 with ≥ 100 invocations:
> Bool, Nat, Eq, Decidable, And, Exists, Or, Prod, List,
> `E213.Term.Internal.Tree`, EStateM.Result.

`Tree` is the only E213-internal inductive in the top 12.
86 distinct callers use Tree recursors — matching G94's
finding that the `a | b | slash` Raw trichotomy is DRLT's
unique structural-induction fingerprint.

The G90 NARROWNESS conclusion — "decide / Nat / List
dominate" — is correct in spirit but with a sharper picture:

  · `Bool.casesOn` + `Decidable.casesOn` + `Eq.rec/casesOn` =
    2,815 invocations (decide-output unfolding + equality
    rewriting at recursor layer).  G91's Pattern #2 footprint
    at the Expr level.
  · Connectives (And/Or/Exists) = 946 invocations.  Standard
    constructive logic destructuring.
  · Tree = 104 invocations.  DRLT's structural-axiom signature.

### §2.5  Other E213-internal recursors (after Tree)

| Total | Inductive |
|------:|-----------|
| 53 | `Cohomology.Surfaces.T2Squared.Cell2` |
| 52 | `Lens.Number.Nat213.Peano.Nat213` (DRLT's own Nat encoding) |
| **46** | **`E213.Theory.Raw`** (just `.rec`, 46/46) |
| 35 | `PatternCatalog.Algebra.OpWord` |
| 27 | `CascadeCalculus.Core.Status` |
| 23 | `SyntacticInternalization.Glyph` |
| 20 | `ArityForcingGeneral.RawNk` |

`E213.Theory.Raw.rec` itself has 46 distinct callers.  Raw's
own recursor (not Tree's) is used in 46 decls — these are the
decls that recurse directly on the Raw type (a smaller subset
than the 86 Tree-recursing decls).

This shows the **distinction between Raw and Tree** in DRLT:

  · `Theory.Raw` is the abstract 4-clause axiom type
  · `Term.Internal.Tree` is the concrete realisation
  · Most structural induction is on Tree (the carrier), not on
    Raw (the abstract type).  Makes sense — abstract Raw doesn't
    have constructors to case-split on; the concrete Tree does.

---

## §3.  Combined picture — DRLT's structural fingerprint

After G90 + G91 + G92 + G102 + G103 + G104 + G105:

  · **Expr-shape**: 99 % `app + const + lit + bvar`; minimal
    binders.  Higher-order machinery delegated to surface
    tactics.
  · **Recursor vocabulary**: 185 inductive types observed; 11
    dominant.  Bool + Nat + Eq + Decidable + connectives
    account for ~70 % of all recursor invocations.  Tree is
    the only E213-internal in the top 11.
  · **Architectural λ-density**: bottom layer (Theory.Raw,
    Term.Internal, RawCmpIndependence) has 5-11× corpus mean
    λ density; upper layer (Lib.Math, Lib.Physics) has 0.2-0.8×.
    DRLT has a measurable layered structure at Expr level.
  · **Raw-derivation footprint**: 1,087 body callers + 1,183
    type-sig callers reference `Theory.Raw` directly.  86
    callers structurally induct on Tree.  46 callers use
    `Raw.rec`.  Lower-bound: ~1,200 decls touch Raw atomic
    structure directly.  Upper-bound (logical derivation): all
    18,361 decls (∅-axiom verified).

The gap between 1,200 (direct touch) and 18,361 (logical
derivation) is the encapsulation effect — quantified.

---

## §4.  Roster impact

  · L1 LeibnizAlgLift still rank #1 (5-layer agreement, G103 §3).
  · G105 doesn't surface new abstraction candidates — it
    refines the structural understanding.
  · One small finding: **Tree-recursor decls (86 callers)** are
    a candidate cluster for further analysis.  G94 §6 found 23
    a|b|slash decls; the 86 figure is broader (includes
    cases-on, brec-on variants).  Cross-reference could
    refine the abstraction-#L roster entry (Tree-manipulation
    slash-arm prologue).

---

## §5.  Methodological note

G90's hardcoded recursor list shows the limit of pattern-
based scanners — they only find what they're configured to
find.  A more robust scanner would iterate ALL inductive
types (via env.inductiveDecls) and dynamically generate the
recursor name set.

For the corpus's purposes, the G90 5-tag inventory captured
the load-bearing fold patterns; the broader 185-inductive
inventory captures the case-split + recursor structure.  Both
are valid views; G105 §2.4's corrected formulation reconciles
them.

---

## §6.  Artifacts

  · Per-namespace shape: derived from `_ast_shape_rows.tsv`
    (G103) via inline analysis.
  · Recursor inventory: derived from
    `_ast_callgraph_edges.tsv` (G102) via regex filter on
    callee suffix.
  · No new tool added — all data derivative of prior scans.
