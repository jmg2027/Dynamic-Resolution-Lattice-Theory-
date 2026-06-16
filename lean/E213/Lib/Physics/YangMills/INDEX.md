# `Lib/Physics/YangMills/` — Yang-Mills + Weinberg-angle structure

Yang-Mills mass gap, SU(5) root structure, W/Z bosons, Weinberg
angle.

## Files (5)

  - `Gap.lean`             — Yang-Mills mass gap: gauge-lattice Laplacian
                             `Δ₀` of `K_{3,2}^{(c=2)}`, complete eigenbasis
                             `{0,4,4,6,10}`, gap `= c·min(NS,NT) = 4 > 0`
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
