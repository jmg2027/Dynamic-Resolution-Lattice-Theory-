# Operation × Topology

**Status**: Closed (4 files, capstone `G48Capstone`).

## Overview

The **operation × topology** cross-axis: 213-native operations
(add, mul, slash, ...) interact with 213-native topologies (sign,
magnitude, quaternion, complex) as a **product structure**, not
as independent layers.  The topological complexity of an
operation is `O(operation_levels · base_topology_complexity)`.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/OperationTopology/` (4 files)
- **Capstone**: `G48Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `OperationLevels` | Operation-by-level decomposition |
| `TopologicalComplexity` | Complexity measure per (op, topology) cell |
| `TotalPreservation` | Total-preservation invariant (op preserves topology) |
| `G48Capstone` | Operation × topology master |

## Narrative

In classical mathematics, operations (+, ×) and topologies
(open sets, metrics) are independent — you can have a group
without a topology and vice versa.  In 213, each operation
**implicitly carries** a topology (the discrete Lens output of
its operation graph), and each topology **implicitly carries**
an operation (the closure operation).

The 4 × N table (op rows × topology columns) at level N:
- Op rows: {add, mul, slash, cup, ...}
- Topology columns: {sign, magnitude, quaternion, complex, ...}
- Cell (op, topology): the complexity of `op` operating in
  `topology`

`TotalPreservation` proves the invariant: an operation in 213
**preserves** its native topology — never moves an element outside
its topological class.  This eliminates the "well-defined on
classes" boilerplate that classical algebra requires.

## Companion clusters

- `Lib/Math/LevelTopology/` (concrete topology per floor — `theory/math/level_topology.md`)
- `Lib/Math/GenerationRule/` (generation rule — `theory/math/generation_rule.md`)
