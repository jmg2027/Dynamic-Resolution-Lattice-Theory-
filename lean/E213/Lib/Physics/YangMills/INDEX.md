# `Lib/Physics/YangMills/` — Yang-Mills + Weinberg-angle structure

Yang-Mills mass gap, SU(5) root structure, W/Z bosons, Weinberg
angle.

## Files (5)

  - `Gap.lean`             — Yang-Mills mass gap
  - `SU5Roots.lean`        — SU(5) root system
  - `WZBosons.lean`        — W and Z boson masses
  - `WeinbergAngle.lean`   — Weinberg angle θ_W
  - `Bridge.lean`          — bridge to other clusters

## Top-level

  - `YangMills.lean` aggregator

## Where to add new files

  - New gauge boson         → `<Boson>.lean`
  - Root system variant     → `<SU(N)>Roots.lean`
  - Symmetry-breaking angle → `<Name>Angle.lean`
