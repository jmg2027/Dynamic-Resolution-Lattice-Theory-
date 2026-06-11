# `Lib/Math/Cohomology/CupAW/` — Alexander-Whitney cup product

The `cupAW` cup product on the 213-native cochain complex:
homotopy-coherent variant that survives the algebraic-lift
constructions (companion to `Cup/`, the strict cup product).

## Files (22)

### Core (5)
  - `Core.lean`         — `cupAW p q : Cochain n p → Cochain n q
                           → Cochain n (p+q)`
  - `Zero.lean`         — `cupAW 0 _ _ = const false`
  - `Pointwise.lean`    — pointwise rewriting rule
  - `Bilinear.lean`,
    `BilinearFunc.lean` — bilinearity in either argument

### Leibniz identities (7)
  - `Leibniz.lean`        — Leibniz rule generic statement
  - `BasisLeibniz.lean`   — Leibniz on basis elements
  - `LeibnizMid.lean`     — middle-degree variant
  - `Leibniz4Mixed.lean`  — 4-mixed-degree case
  - `Leibniz21Bridge.lean`,
    `Leibniz21Final.lean` — (2, 1)-bridge + final form
  - `Leibniz22Bridge.lean`,
    `Leibniz22Final.lean` — (2, 2)-bridge + final form

### Pointwise / scaling (2)
  - `PointwiseBilinear.lean` — pointwise + bilinear fusion
  - `LeibnizScaling.lean`    — scaling form
  - `LeibnizSmall.lean`      — small-input specialisation

### Algebraic-lift bridges (5)
  - `LeibnizAlgLift.lean`           — generic algebraic lift
  - `LeibnizAlgLift21.lean`,
    `LeibnizAlgLift21Alpha.lean`   — (2,1) lift + α variant
  - `LeibnizAlgLift22.lean`,
    `LeibnizAlgLift22Alpha.lean`   — (2,2) lift + α variant

## Top-level

  - `CupAW.lean` aggregator
  - `UniversalFamilyCapstone.lean` — CupAW universal-Leibniz family closure capstone

## Status

Two files (`LeibnizScaling`, `LeibnizSmall`) historically deferred
due to `Universal.Prop31.pattern_eq` rename — check current build
status before use.

## Where to add new files

  - New Leibniz shape          → `Leibniz<dim>*` style
  - Algebraic lift             → `LeibnizAlgLift<dim>*`
  - Bridge / final pair        → `Leibniz<dim>Bridge` /
                                  `Leibniz<dim>Final`

## Companion clusters

  - `Cup/`       — strict cup product
  - `Cochain/`   — cochain base type
  - `Universal/` — Prop31 / Universal AW lifts
