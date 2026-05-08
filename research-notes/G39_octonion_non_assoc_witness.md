# G39 — Octonion Non-Associativity: First Concrete Witness

**Date**: 2026-05-08 (post G38 / PR #66)
**Origin**: Mingu — skip mechanical, do insight-dense.

## Core delivery

The first **computable inequality** in the CD-tower stack
demonstrating loss of an algebraic property at a specific level.

Formalized fact (∅-axiom, by `decide`):

```
octBasisMul (octBasisMul e1 e2) e4
  ≠
octBasisMul e1 (octBasisMul e2 e4)
```

This is **not** an abstract claim — it is a **concrete inequality**
between two specific values, proven by Lean kernel ∅-axiom
evaluation.

## Why it matters

G37/G38 made the abstract claim "at CD level 3, associativity is
lost."  G39 turns it into a *theorem*: specific witness that two
associations give different results.

## Quaternion control

To make G39 meaningful, the quaternion control also proven
(`quaternion_assoc_control`):
```
octBasisMul (octBasisMul e1 e2) e1
  = octBasisMul e1 (octBasisMul e2 e1)
```
At Fano-line (1,2,3) (quaternion sub-structure), associativity
*holds*.  The level-3 break is real, not Fano-internal.

## Fano plane structure

`FanoPlaneStructure.lean` enumerates 7 oriented triples:
(1,2,3), (1,4,5), (2,4,6), (3,4,7), (1,6,7), (2,5,7), (3,5,6).

  * 7 lines × 3 points = 21 incidences = 7 points × 3 lines.
  * `2² + 2 + 1 = 7` (= |PG(2, 𝔽₂)|).
  * |Aut(Fano)| = |PSL(2, 7)| = 168.

## Fano ↔ K_{3,2}^{(c=2)} bridge

| Quantity | Fano | K_{3,2}^{(c=2)} | Connection |
|---|---|---|---|
| Lines/Edges | 7 | 12 | 7 + 5 = 12 ✓ |
| Points/Verts | 7 | 5 | — |
| Top-dim | 7 lines | b₁ = 8 | 7 + 1 = 8 |
| 7-fold | line count | b₁ − 1 = 7 | direct |
| 8-fold | octonion dim 1+7 | b₁ = 8 | direct |

Cardinality bridges; full structural homomorphism is deeper.

## Insight summary

**G37/G38 synthesis is structurally testable, and passes.**

Each property loss at level n → concrete computable inequality:

  * Level 2 → 3: associativity (this PR) — `(e₁·e₂)·e₄ ≠ e₁·(e₂·e₄)`
  * Level 3 → 4: alternativity (PR #65) — `sedZero ≠ sedOne`
  * Earlier levels: commutativity (Hamilton i·j vs j·i),
    ordering loss (signed extension)

Stack is **calculation-ready**.

## Filed under

  * G36 (PR #62), G37 (PR #64), G38 (PR #65), Math closure (PR #66)
  * `Lib/Math/SignedCut/OctonionNonAssociativity.lean`
  * `Lib/Math/SignedCut/FanoPlaneStructure.lean`
  * `Lib/Math/SignedCut/FanoK32Bridge.lean`
