# Dialogue Audit — Provable vs Heuristic (G43)

**Status**: Closed (4 files, capstone `G43Capstone`).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 — G43 → chapter + archive.  G43's session-bound name
("dialogue audit") is preserved at the Lean side (`Math/DialogueAudit/`)
but the chapter title clarifies the actual content.

## Overview

A 213-internal **audit primitive** distinguishing what is
**provable in 213** (formal Lean theorem) from what is
**heuristic** (numerical match, structural suggestion).

The four sub-witnesses formalize the audit categories: axis
distinction, bit precision, pigeonhole finite-state count, and
overall G43 capstone.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/DialogueAudit/` (4 files)
- **Capstone**: `G43Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `AxisDistinction` | NS-axis vs NT-axis distinction primitive |
| `BitPrecision` | Bit-precision audit (information content) |
| `PigeonholeFiniteState` | Finite-state pigeonhole counting |
| `G43Capstone` | Dialogue audit master |

## Narrative

In session dialogue (between Mingu and Claude), claims often come
in three flavors:

1. **Provable** — has a Lean theorem witness
2. **Structural-suggestion** — a pattern observed in derived numbers
3. **Heuristic-only** — numerical match without underlying structure

The audit primitives separate these by mechanical decision.
`AxisDistinction` ensures spatial vs temporal claims stay
distinguishable; `BitPrecision` measures the information-content
floor of a claim; `PigeonholeFiniteState` counts the cases that
must be exhausted for a "provable" classification.

The result is a **decidable audit category** for every
session-level claim — a meta-tool preventing heuristic claims
from drifting into "we proved it" status.

## Research-note provenance

`research-notes/G43_dialogue_audit.md` — archived.

## Open frontier

Could be extended with **citation-graph auditing** (G92 meta-scan
adjacent) to mechanically flag dialogue claims whose Lean
references don't resolve.
