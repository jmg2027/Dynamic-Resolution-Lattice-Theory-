# G49 — Concrete Topology per Floor

**Date**: 2026-05-08 (post G48)
**Origin**: Mingu's request for concrete examples + CD tower
correction.

## Concrete topology per floor

| Floor | CD lvl | Operation | Topology | Picture |
|---|---|---|---|---|
| 1 | 0 | magnitude | trivial point | ● |
| 2 | 1 | sign | K₂ bipartite | ●─● |
| 3 | 2 | i | Z/4 cycle | 4-cycle |
| 4 | 3 | j, k | K₃ oriented | i→j→k→i |
| 5 | 4 | octonion | Fano plane (G39) | 7 lines |

## Tower divergence

Mingu's correction: classical CD treats sign as INTERNAL to
ℝ.  213 separates magnitude from sign:

| 213 floor | Classical CD | Content |
|---|---|---|
| Floor 1 | (none) | Cut (positive magnitude) |
| Floor 2 | Level 0 (ℝ) | SignedCut |
| Floor 3 | Level 1 (ℂ) | ComplexCut |
| Floor 4 | Level 2 (ℍ) | Quaternion |

213's floor 1 = magnitude-vs-sign distinction lost in ZFC's ℝ.

## Floor-by-floor pictures

**Floor 1 (point)**: `|x|` for x≥0.  Single trivial node.

**Floor 2 (K₂)**: `(Pos, Neg)` pair, sign flip is the edge.

```
  Pos ●─────● Neg
```

**Floor 3 (Z/4 cycle)**: powers of i = {1, i, -1, -i}.

```
      1
    ╱   ╲
  -i     i      (multiply by i = step)
    ╲   ╱       (i⁴ = 1, closes cycle)
     -1
```

**Floor 4 (K₃ oriented)**: imaginary {i, j, k}, cyclic
i→j→k→i positive orientation.  Reversal = sign flip.

**Floor 5 (Fano plane)**: 7 oriented triples encoding the
octonion multiplication table (G39).

## Pattern

| Floor | Nodes | Edges |
|---|---|---|
| 1 | 1 | 0 |
| 2 | 2 | 1 |
| 3 | 4 | 4 |
| 4 | 3 | 3 |
| 5 | 7 | 7 |

Note: K₃ at floor 4 has fewer raw nodes than Z/4 at floor 3,
but the K₃ orientation/non-commutativity adds structural
complexity.  "Topological complexity" is not just node count.

## Modules (5 .lean + 1 capstone, all ∅-axiom)

  * `MagnitudeTopology.lean` — Floor 1
  * `SignTopology.lean` — Floor 2
  * `ComplexTopology.lean` — Floor 3
  * `QuaternionTopology.lean` — Floor 4
  * `TwoTowersDivergence.lean` — 213 vs classical
  * `G49Capstone.lean` — 5 cluster witnesses

## Filed under

  * G36-G48 (PRs #62-#76)
  * G39 Fano plane (Floor 5 topology)
