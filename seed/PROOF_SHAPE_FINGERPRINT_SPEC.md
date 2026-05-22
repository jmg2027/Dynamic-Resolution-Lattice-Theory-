# Proof-shape fingerprint spec (TH-1)

How the 213 corpus identifies proof-shape clusters, what the fingerprint
captures, and what consolidation it enables.  Companion to TH-2
(`RAW_DERIVATION_SPEC.md`), TH-3 (`FALSIFIABILITY_SURFACE_SPEC.md`),
and TH-4 (`L1_PARAMETRIC_METHODOLOGY_SPEC.md`).

## What is a "proof-shape fingerprint"?

A fingerprint of a proof is a normalized abstraction that captures its
structural pattern while ignoring per-instance content:

  · **Tactic token sequence** (G91): the ordered list of top-level
    tactic names — `[intro, apply, show, constructor, intro, have, ...]`.
  · **Expr-node shape** (G103): the AST shape after `unfold` and
    `simp`-normalisation, as a multiset of constructor/elim tags.
  · **Recursor invocation set** (G105): which inductive types' `.rec`
    or `.casesOn` are called inside the proof body.
  · **Citation graph** (G92 / G102): which other theorems are
    `exact`-applied or `rw`-rewritten.

Two proofs are **byte-identical at fingerprint level** when they share
all four projections.  A 2-sibling group exists when both proofs in the
pair share their fingerprint but differ in surface text (variable
names, specific Nat literals).

## Source catalogs

The canonical fingerprint inventory is split across:

  · `catalogs/recursor-inventory.md` — 185 inductive types × recursor
    invocations (G105).  The recursor set is the most stable
    discriminator (re-running the scanner is deterministic).
  · `catalogs/internal-hubs.md` — top E213-internal load-bearing
    lemmas by citation count (G92 surface + G102 Expr).
  · `catalogs/falsifier-roster.md` — 135 `by decide` falsifier-style
    proofs (G100), grouped by negation shape.
  · `catalogs/cross-domain-identifications.md` — 109 cross-namespace
    byte-identical-shape groups (G109), 25 of which are substantive
    math↔physics bridges.
  · `lean/E213/ARCHITECTURE.md` NAV-3 note — empirical-verification
    fact that `Bool.casesOn` (1,681 invocations) was missing from
    G90's hardcoded 5-tag list, leading to the G105 correction
    (185 inductive types, not 5).

## What the fingerprint enables

**Consolidation candidates**: when N proofs share fingerprint, an
abstraction is warranted.  The Part 3 + Part 4 + Part 5 marathon
absorbed 280+ sites across 12 templates (L1, L2, C, FLUX-1,
COH-1/2/3, L3, L4, Pell-FSM, ModArith, M-recursor, Pattern10,
InvolutionTemplate).  Each template was surfaced by a
fingerprint-cluster scan.

**Mass tracking**: Expr-node mass (G103) gives a numeric metric for
"how much elaboration would be retired" if a template absorbed the
cluster.  L1 α/β-side at 6.6M chars and FLUX-1 at 30K nodes
were the largest single consolidations.

**Cross-domain bridges**: when fingerprint clusters span math vs.
physics namespaces (G109), the bridge IS the equation.  CDI-5
(physics atomic-bracket containment) is 8 distinct
"observed constant X in DRLT-bracket [low, high]" proofs that are
byte-identical post-normalisation.

## How to re-run the scanner

```bash
python3 tools/syntax_tactic_scan.py     # G91 surface tactic motifs
python3 tools/ast_callgraph_scan.py     # G102 Expr-level call graph
python3 tools/ast_shape_scan.py         # G103 shape density + L1 zones
python3 tools/syntax_rw_cascade_scan.py # G99 rw-cascade k-grams (adoption gap)
python3 tools/falsifier_mining_scan.py  # G100 by-decide falsifier catalog
python3 tools/ast_typesig_scan.py       # G104 type-sig + sort-universe
python3 tools/ast_callgraph_scan.py     # G102 recompute
```

Each scanner writes a cached TSV to `tools/_<scan_name>_rows.tsv`
(see `.gitignore`).  Re-runs are deterministic.

## Cross-references

  · `seed/META_SCAN_ARCHETYPES.md` — 11 scanner archetypes + dual-branch
    process model.
  · `seed/RAW_DERIVATION_SPEC.md` — TH-2 (α/β/γ readings).
  · `seed/FALSIFIABILITY_SURFACE_SPEC.md` — TH-3 (quantitative §5.2.1).
  · `seed/L1_PARAMETRIC_METHODOLOGY_SPEC.md` — TH-4 (L1 closure pattern).
  · `LESSONS_LEARNED.md` Patterns #1-#20.
  · `research-notes/G107_action_items_registry.md` — full registry.
  · `research-notes/G101_metascan_synthesis.md` — capstone synthesis.

## When this spec is reused

When a future marathon surfaces a new fingerprint cluster, follow
TH-1 → TH-4 chain:

  1. **TH-1 (this spec)**: run scanners, identify cluster.
  2. **TH-2 (RAW_DERIVATION_SPEC)**: verify the cluster is α/β-derivable
     (not just structural duplication).
  3. **TH-3 (FALSIFIABILITY_SURFACE_SPEC)**: check that the
     abstraction preserves the falsifier surface (does not add axioms).
  4. **TH-4 (L1_PARAMETRIC_METHODOLOGY_SPEC)**: extract the parametric
     helper; per-instance corollaries become 1-line calls.
