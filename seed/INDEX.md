# seed/ — DRLT 213 axiomatic + philosophical foundation

This directory contains the **non-Lean** foundational documents:
the axioms (English), philosophy, falsifiability claims, and
the DRLT origin narrative.  Most subsequent formalization in
`lean/E213/` is the formal counterpart of statements first
made here in prose.

## Reading order (for new arrivals)

| # | File | What it does | When to read |
|---|---|---|---|
| 1 | `ORIGIN.md` | DRLT origin story — minimal residue, 4-clause Raw axiom | First |
| 2 | `AXIOM.md` | The axiom in English: relations, distinctness, /, depth | After ORIGIN |
| 3 | `PHILOSOPHY.md` | Position of the axiom; "primitive distinction" as primitive (not "relation"); 213 above every framework that points; linguistic inevitability + minimum-commitment expressions; derive-not-reconcile; status of "something" left open | Before any Real213 work |
| 3a | `RESOLUTION_LIMIT_SPEC.md` | Canonical mechanical-spec: cardinality as lens output, N_U as four-domain convergent invariant, type-preservation under ∅-axiom (Cantor + Cauchy) | Before any Real213 work |
| 4 | `NOTATION.md` | Symbol conventions: NS, NT, d, c, α_GUT, K_{3,2}^{(2)} | Reference |
| 5 | `FALSIFIABILITY.md` | 14 measurement propositions that would refute DRLT | When discussing experimental tests |
| 6 | `IMPLEMENTATION.md` | Mapping seed → `lean/E213/Theory/Raw` | When tracing axiom-to-code |
| 7 | `AUDIT_Lean.md` | Audit guide for verifying Lean ↔ seed correspondence | When auditing |
| 8 | `PAPER1.md` | Original seed paper (Raw + Lens, ZFC commitments, Cauchy completeness, demonstrations, falsifiability) — broader than `lean/E213/Lib/Math/Cohomology/Paper1Chiral.lean` (which only covers chiral compression).  Substantive narrative kept. | Historical / reference |

## What seed/ is NOT

- **NOT the source of truth.**  `lean/E213/` is.  When seed and
  Lean disagree, Lean wins.
- **NOT a reading order for the actual mathematics.**  For that,
  see `guide/INDEX.md` (deductively-ordered narrative).
- **NOT a paper draft.**  See `papers/README.md` (deprecated
  archive — content moved to Lean + guide).

## Naming policy: 213 / DRLT / E213 (canonical)

| Name | Meaning | Where used |
|---|---|---|
| **213** | the formal axiom framework — Raw + 4-clause axiom + Lens framework + ∅-axiom commitment.  The mathematical / type-theoretic side. | seed/AXIOM.md uses "213 axiom" throughout; metatheorems and Lean tree are about 213. |
| **DRLT** | "Dynamic Resolution Lattice Theory" — the physics deployment of 213.  Coined from the Zeno → pixels intuition (`ORIGIN.md` §3, table line "Zeno → pixels  →  DRLT's 'Dynamic Resolution' name"). | Physics constants table (CLAUDE.md), `Physics/` Lean tree, papers, "DRLT zero-parameters" capstones. |
| **E213** | the Lean namespace.  Mechanical artifact (`namespace E213.Theory`, `namespace E213.Lens`, …). | Lean source only. |

**Disambiguation rule.** Use **213** when discussing the axiom or
mathematical framework (Raw, Lens, ∅-axiom standard, AXIOM.md, …).
Use **DRLT** when discussing physics (constants, observables,
predictions, the lattice/resolution picture from ORIGIN.md).  Use
**E213** only inside Lean code or when referring to specific
Lean modules.  When in doubt about a math/physics-boundary claim,
prefer **213** (it's the broader name; DRLT is a physics
specialization of 213).

## Cross-references

- `lean/E213/Theory/Raw*.lean` — formal counterpart of `AXIOM.md`
- `lean/E213/Theory/Atomicity/Five.lean` +
  `lean/E213/Theory/Atomicity/PairForcing.lean` — formal
  counterpart of "atomicity forces (NS=3, NT=2, d=5)".
  (These were previously at `OS/` until 2026-05-XX dissolution;
  see `lean/E213/ARCHITECTURE.md` for theory.)
- `lean/E213/Lib/Physics/Foundations/FiniteUniverse.lean` — formal
  counterpart of `RESOLUTION_LIMIT_SPEC.md` (1/α_em rational at every
  finite N_U; π² is limit-label, not a 213 primitive)
- `LESSONS_LEARNED.md` (root) — guardrails extending PHILOSOPHY.md
- `lean/E213/ARCHITECTURE.md` — canonical layer architecture
  (where Firmware/Atomicity sub-cluster sits in the dependency graph)

## Status

  - `ORIGIN.md`, `AXIOM.md`, `PHILOSOPHY.md`, `NOTATION.md`: stable
  - `IMPLEMENTATION.md`, `AUDIT_Lean.md`: should track Lean refactors
  - `PAPER1.md`: archival reference, not actively maintained.  Still
    cited from ~25 Lean files via `PAPER1 §X.Y` markers — do not delete.
