# Meta-scan archetypes + dual-branch process model

Reference document for static-analysis tasks on the E213 corpus.
Pointed-to from `CLAUDE.md`.  Produced by the meta-analysis
branch `claude/analyze-lean4-ast-patterns-49Rh2` through
2026-05-22.

---

## 11 reusable scanner archetypes

Future static-analysis work should pick from this set + customise
per question rather than starting from scratch.

| # | Archetype | Tool | Use case |
|--:|-----------|------|----------|
| 1 | Tier-2 AST motif scanner | `tools/ast_fold_scan.py` + body | Pattern-counting at elaborated layer; fold/recursor sites |
| 2 | Tier-1 syntax skeleton scanner | `tools/syntax_tactic_scan.py` | Tactic-style fingerprint; ladder detection |
| 3 | Tier-1.5 citation graph + construct extractor | `tools/syntax_arg_scan.py` | Dependency graph; construct distribution |
| 4 | Targeted ±N context dumper | `tools/syntax_arg_scan.py --context-target <lemma>` | Surrounding patterns of specific hub |
| 5 | Multi-def unfold-chunk scanner | `tools/syntax_unfold_scan.py` | Implicit-lemma discovery via co-unfold |
| 6 | k-gram cascade miner | `tools/syntax_rw_cascade_scan.py` | Adoption-gap detection (Pattern #10) |
| 7 | Falsifier mining | `tools/falsifier_mining_scan.py` | "What cannot be" surface (Pattern #13) |
| 8 | Full Expr call graph extractor | `tools/ast_callgraph_scan.py` + body | Mechanical dependency graph |
| 9 | Expr-shape density extractor | `tools/ast_shape_scan.py` + body | Architectural λ-density; heaviest-decl identification |
| 10 | Type-signature dependency + sort | `tools/ast_typesig_scan.py` + body | Type-layer dependency; Prop vs Type distribution |
| 11 | Shared helper | `tools/lean_syntax_parse.py` | `strip_comments`, `find_decl_bodies`, `walk_e213_files` |

Each scanner (where applicable) accepts `--report-only` for
instant re-cluster against cached TSV.  TSVs are gitignored;
regenerable via the corresponding `tools/*.py` invocation.

**When in doubt**: consult this list before writing new tooling
for "find all X that share property Y in the corpus".

---

## Dual-branch process model

The meta-analysis branch + parallel substantive branch
(`claude/subset-bijection-lemmas-w2FKf`) cycle through cross-branch handshakes demonstrated a working
collaborative pattern:

  · **Meta branch** — scans + pattern surfacing + research
    notes + cross-references.  Does NOT execute substantive
    PURE-theorem changes.
  · **Substantive branch** — PURE theorem additions, abstraction
    execution, math marathons.  Uses meta-branch findings as
    input.
  · **Handshake docs** — the handshake research notes research notes
    explicitly addressed cross-branch.  Format: §C1..§Cn proposal
    items, the receiving side responds with done/deferred/declined.

This pattern **avoids merge conflicts** (each branch only
modifies its own area) while enabling **bidirectional
information flow** (meta surfaces, substantive executes).

Generalises to any static-analysis-heavy task: future audits
(purity-check, layer-audit, lessons-mining, ...) can follow the
same separation.

---

## Anchor research notes

  · `research-notes/archive/metascan/G101_metascan_synthesis.md` —
    capstone overview (6-scanner unified view + honest assessment of
    what was/wasn't found).
  · `research-notes/archive/metascan/G107_action_items_registry.md` — executor
    entry-point (14 Lean abstraction candidates + 13 doc-work
    items, all ranked by priority).
  · the per-subtree deep-dive research notes — per-subtree Tier-2/3 deep
    dives (Real213/Analysis, FluxMVT, Cohomology,
    HodgeConjecture, DyadicFSM, CayleyDickson — ~6,400 decls).
  · `LESSONS_LEARNED.md` Patterns #10-#17 — methodological
    findings from the meta-analysis branch.

---

## Catalogs (lookup-table consolidations)

  · `catalogs/cross-domain-identifications.md` — 10 CDIs
    (math ↔ physics byte-identical Expr from cross-domain identification scan).
  · `catalogs/recursor-inventory.md` — 185 inductive types
    using recursors.
  · `catalogs/internal-hubs.md` — top E213-internal load-bearing
    lemmas (citation-graph + Expr-level callgraph surfaces).
  · `catalogs/falsifier-roster.md` — 135 decide-verified
    impossibility theorems (automated decide-failure mining).

---

## When to invoke

Static-analysis tasks where this document applies:
  · "Find all decls that share X" — pick the matching archetype.
  · "Why is property P over the corpus?" — pick the archetype
    that surfaces P.
  · "Refactor candidate audit" — use archetype 6 (k-gram
    cascade) + archetype 9 (Expr shape) + Pattern #11 (n-layer
    agreement = abstraction inevitability).
  · "Cross-domain identification check" — use shape-vector
    grouping over Expr-shape density data + cross-namespace filter (the cross-domain identification scan).

Sit out from THIS document when the task is substantive Lean
theorem development — that's the substantive-branch role.
