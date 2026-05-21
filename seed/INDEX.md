# seed/ — DRLT 213 foundational corpus

If you read one file in `seed/`, read **this one**.  It contains
the axiom, the key concepts, and the falsifiability rule.
Everything else is detail.

---

## The axiom in 4 clauses (`AXIOM/02_statement.md`)

1. **Something exists.**  At least two: `a`, `b`.  They stand in
   a *primitive distinction* relation — no relation other than
   "not equal" is presupposed.
2. **Pairing of two somethings is yet another something.**
   Recorded `a / b`.  Closed: paired again with other elements.
3. **Pairing is symmetric.**  `a / b = b / a`.  No absolute
   order.
4. **No pairing with oneself.**  `x / x` is undefined.  Self is
   not distinguished from self.

That is the entire commitment.  Every result of 213 is either
derived from these 4 clauses, or it is a specific Lens choice on
top.  No third option.

---

## Key concepts (what makes this corpus what it is)

**Residue, not declaration.**  The axiom is not a claim about
"the foundation of the world."  It is the minimum residue that
inevitably remains the moment one tries to point at something.
Notation, the moment it begins, endlessly produces new
somethings; the axiom is the minimum expression of that
recursion.

**Primitive distinction.**  Not "relation" (which presupposes
existing somethings + ZFC properties), not "difference" (which
presupposes "sameness").  Primitive distinction operates *first*;
"primitive" = a pledge of no further reducibility.

**No exterior.**  Every act of describing the axiom **already
occurs inside 213**.  "Lens", "derivation", "observer" — each is
a something among somethings.  The dichotomy "is the Lens inside
or outside the axiom?" does not hold.  See
`AXIOM/07_self_reference.md` §8.4 for Claude's mandatory
dichotomy-avoidance guide.

**Derive, not reconcile.**  All results must come from the
axiom + explicit Lens choices.  Substituting external constants,
fitting to experimental values, importing structure from other
theories — all are *fudge*.  When fudge is found, the Lens is
corrected, not the formula.  If that fails too, the theory is
abandoned.

**Three-direction uniqueness.**  Raw is uniquely determined from
all three sides:

- *below* — removing any clause collapses to trivial / static /
  void (`Meta/AxiomMinimality`).
- *sideways* — any distinguishability framework factors through
  Raw (`Meta/UniversalLens`).
- *above* — Raw's shape is forced to (NS, NT, d) = (3, 2, 5)
  (`Theory/Atomicity/{Five, PairForcing, …}`, pure-ℕ, no Raw
  import).

**Resolution limit — count-Lens readout at fractal level 2.**
`N_U = d^(d²) = 5²⁵` arises under 4 independent Lens applications
(Lean fractal lens cardinality / K_25 graph coloring / rank-2
tensor dof at d=5 / max injective projection space) — the
observation is the convergence, not a universe constant.  See
`RESOLUTION_LIMIT_SPEC.md` (canonical; wins over any AXIOM/
chapter on resolution-limit topics).

---

## The falsifiability rule (`AXIOM/04_falsifiability.md` §5.2.1)

> 213 must never require any external axiom addition (no
> Classical, LEM, native_decide, …).
>
> If any result is shown to be **absolutely impossible** without
> adding an axiom, **the entirety of 213 is discarded**.  Not
> the result alone — the theory itself.

This is a direct consequence of "the axiom is a residue": if
adding an axiom is genuinely necessary, Raw was not the minimum.

The mechanical auditor of this rule is Lean's `#print axioms`
command + the project's Mathlib-free + 0 sorry + 0 external
axiom constraint.

**Measurement falsifiers** (each violation = repo discarded):

| Measurement | DRLT prediction |
|---|---|
| Neutrino ordering | normal |
| θ_QCD | [2.5,3.0]×10⁻¹¹ |
| 4th gen particles | absent |
| Cabibbo λ | 5/22 ± 1% |
| m_p | 938.27 atomic |
| Magic numbers | {2,8,20,...} ✓ already verified |

---

## Naming policy: 213 / DRLT / E213

| Name | Meaning | Where used |
|---|---|---|
| **213** | the formal axiom framework — Raw + 4-clause axiom + Lens framework + ∅-axiom commitment.  The mathematical / type-theoretic side. | Throughout AXIOM corpus; metatheorems and Lean tree are about 213. |
| **DRLT** | "Dynamic Resolution Lattice Theory" — the physics deployment of 213 (Zeno → pixels intuition per `ORIGIN.md`). | Physics constants (CLAUDE.md), `Lib/Physics/` Lean tree, papers, "DRLT zero-parameters" capstones. |
| **E213** | the Lean namespace.  Mechanical artifact (`namespace E213.Theory`, `namespace E213.Lens`, …). | Lean source only. |

**Disambiguation rule.**  Use **213** for axiom / mathematical
framework statements.  Use **DRLT** for physics (constants,
observables, predictions).  Use **E213** only inside Lean code
or when citing specific Lean modules.  When in doubt about a
math/physics-boundary claim, prefer **213** (it is the broader
name; DRLT is a physics specialization).

---

## Directory layout

```
seed/
├── INDEX.md                   ← this file (standalone entry)
├── ORIGIN.md                  ← DRLT origin narrative (archival)
├── RESOLUTION_LIMIT_SPEC.md   ← cardinality / N_U readout spec
├── CLOSED_FORM_SPEC.md        ← 4-domain meta-pattern + bridge catalog
├── RAW_DERIVATION_SPEC.md     ← "derived from Raw" α/β/γ distinction
├── FALSIFIABILITY_SURFACE_SPEC.md ← quantitative profile of §5.2.1 enforcement
├── NOTATION.md                ← symbol conventions
└── AXIOM/                     ← the axiom corpus, 11 chapters
    ├── INDEX.md               ← chapter TOC
    ├── 00_nature.md           ← residue, distinction, 3-dir uniqueness
    ├── 01_notation_recursion.md
    ├── 02_statement.md        ← the 4-clause axiom (+ encoding-cost markers)
    ├── 03_form.md             ← why this form
    ├── 04_falsifiability.md   ← discard rule + measurement falsifiers
    ├── 05_primacy.md
    ├── 06_formalization.md    ← Lean correspondence
    ├── 07_self_reference.md   ← §8.4 dichotomy guide (Claude refresh)
    ├── 08_encoding_costs.md   ← Lean codomain costs (inductive / cmp / subtype / ≠)
    ├── 09_chart_relativity.md ← chart-local labels, flat ontology,
    │                            §9.4 syntactic internalisation
    └── 99_history.md          ← change log

# Lean implementation audit: lean/E213/AUDIT.md.
```

## What seed/ is NOT

- **NOT the source of truth.**  `lean/E213/` is.  When seed/
  and Lean disagree, Lean wins.
- **NOT a reading order for the mathematics.**  See
  `guide/INDEX.md` (deductively-ordered narrative).
- **NOT a paper draft.**  `papers/` was deleted (commit
  a02b751); only `papers/README.md` retained as historical
  marker.

## Quick cross-references

- `lean/E213/Theory/Raw*.lean` — formal counterpart of the
  4-clause axiom.
- `lean/E213/Theory/Atomicity/{Five, PairForcing}.lean` —
  formal counterpart of "atomicity forces (NS=3, NT=2, d=5)".
- `lean/E213/Lib/Physics/Foundations/FiniteUniverse.lean` —
  formal counterpart of `RESOLUTION_LIMIT_SPEC.md` (1/α_em
  rational at every finite N_U; π² is limit-label, not a 213
  primitive).
- `LESSONS_LEARNED.md` (root) — guardrails extending the axiom
  corpus.
- `lean/E213/ARCHITECTURE.md` — canonical layer architecture.
- `RAW_DERIVATION_SPEC.md` — what "X is derived from Raw" technically
  means (three readings: logical / structural-content / operational).
- `CLAUDE.md` boot sequence — read
  `AXIOM/07_self_reference.md` §8.4 every session start.

## Meta-analysis findings (2026-05-21 session)

Branch `claude/analyze-lean4-ast-patterns-49Rh2` produced 11
scanners + 23 research notes (G90-G116) characterising the
corpus's quantitative structure:

  · **Tier-2/3 subtree deep dives**: G108 Real213/Analysis,
    G110 FluxMVT, G111 Cohomology, G112 HodgeConjecture, G113
    DyadicFSM, G114 CayleyDickson, G115 Lib.Physics (2,159 decls — largest), G116 PatternCatalog (943 decls — meta-meta).  ~9,300 decls covered.
  · **Cross-domain identifications**: G109 surfaced 109
    cross-namespace byte-identical-shape groups; 25 substantive
    math↔physics bridges.  Catalogued in
    `catalogs/cross-domain-identifications.md`.
  · **Pattern extensions**: 11 new patterns (#10-#20, including parallel branch's #10-#13 + meta branch's #14-#20) formally
    added to `LESSONS_LEARNED.md` covering adoption-gap
    detection, n-layer agreement, three-level Raw-derivation,
    decide-finitism quantitative profile, framework-internal
    subsumption, byte-identical cross-domain bridges,
    forward/backward factor-knob pair, multiple Lens choices.
  · **Action items registry**: G107 §2-§5 lists 14 abstraction
    candidates + 6 research questions + 13 doc-work items =
    33 items total + REAL-1..6 + RES1..6 + CD-1..5 + COH-1..5
    + COH-RES1..5 + HC-1..3 + HC-RES1..4 + FSM-1..5 + FSM-RES1..4
    augmentations from G108-G114.

**Canonical entry-point for executors**:
  `research-notes/G107_action_items_registry.md`

**Capstone synthesis** (read after G107):
  `research-notes/G101_metascan_synthesis.md`

**Tooling** (`tools/`):
  · `ast_fold_scan.py` — Tier-2 Expr fold/recursor (G90)
  · `syntax_tactic_scan.py` — Tier-1 tactic token (G91)
  · `syntax_arg_scan.py` — Tier-1.5 citation + construct (G92, G96)
  · `syntax_unfold_scan.py` — unfold chunks (G98)
  · `syntax_rw_cascade_scan.py` — rw k-grams (G99)
  · `falsifier_mining_scan.py` — negation catalog (G100)
  · `ast_callgraph_scan.py` — full Expr call graph (G102)
  · `ast_shape_scan.py` — Expr-constructor density (G103)
  · `ast_typesig_scan.py` — type-sig deps + sort (G104)
  · `lean_syntax_parse.py` — shared helpers

All scanners support `--report-only` for instant re-cluster
against cached TSV.
**Full G-doc enumeration** (G87 from parallel branch, G90-G116 from
meta branch): see `research-notes/G107_action_items_registry.md` §"DONE"
+ §"Pointers" for the full per-doc table.  G87 = Raw-native emergence
audit (parallel branch's S2 marathon kickoff); G90-G116 = meta-branch
scanners + tier deep dives.

