# `SignedCut/Bridge/` — signed-cut external bridges

Bridges from signed-cut to Fano plane / K_{3,2} / generic-geometry
structures.

## Files (5)

  - `Bridge.lean`                — generic bridge entry
  - `BridgeCapstone.lean`        — bridge capstone
  - `FanoK32Bridge.lean`         — Fano ↔ K_{3,2}^{(c=2)} bridge
  - `FanoPlaneStructure.lean`    — Fano plane combinatorial structure
  - `GenericGeomBridge.lean`     — generic geometric bridge

## Bridge discipline (CLAUDE.md)

Anti-corruption layer pattern: external vocabulary (Fano plane,
generic geometric terms) stays inside the bridge; signed-cut
results re-stated in 213-native form.

## Where to add new files

  - Bridge to geometric object X    → `<X>Bridge.lean`
  - External structural object      → `<X>Structure.lean`
