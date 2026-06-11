# `CayleyDickson/Tower/` — Cayley-Dickson tower machinery

Generic Cayley-Dickson doubling/tower machinery: CDDouble functor
(level n → level n+1), order-4 monopoly proofs at multiple
levels, asymptotic + fixed-point + universal-induction structure.

## Files (13)

### CD doubling core
  - `CDTower.lean`           — base CD tower carrier
  - `CDDouble.lean`          — CD doubling functor (level n → n+1)
  - `F2CDTower.lean`         — F₂-coefficient CD tower

### Universal-order growth + induction (3)
  - `UniversalInduction.lean`     — universal-induction principle
  - `UniversalOrderGrowth.lean`   — universal-order growth
  - `UniversalOrderGrowthC.lean`  — coefficient variant

### Order-4 monopoly (3, level-stratified)
  - `Order4Monopoly_L4T.lean`     — level-4 (4-tuple)
  - `Order4Monopoly_L5T.lean`     — level-5 (5-tuple)
  - `Order4Monopoly_L6T.lean`     — level-6 (6-tuple)

### Asymptotic + fixed point (3)
  - `AlgebraTowerAsymptote.lean`  — asymptotic growth
  - `AlgebraTowerCapstone.lean`   — capstone result
  - `TowerFixedPoint.lean`        — fixed-point theorem
  - `FirstSlashGrounding.lean` — the "disc −2 skip" descends to the residue's first distinguishing

## Structural drop pattern (CDTower.lean)

| Layer | Axiom that DROPS here |
|-------|----------------------|
| 0 (ZI)         | — (baseline: all R-conditions hold) |
| 1 (Lipschitz)  | R2 (commutativity)           |
| 2 (Cayley)     | associativity                |
| 3 (Sedenion)   | R3 (no zero divisors)        |

## Companion clusters

  - `CayleyDickson/Integer/`    — concrete integer codomains
  - `CayleyDickson/Levels/`     — Cayley + Sedenion level details
  - `CayleyDickson/Lipschitz/`  — Lipschitz level

## Where to add new files

  - New level monopoly        → `Order<N>Monopoly_L<level>T.lean`
  - Universal induction step  → `UniversalInduction*` /
                                 `UniversalOrderGrowth*`
  - CD doubling extension     → `CDDouble*` / `CDTower*`
  - Asymptotic / fixed-point  → `AlgebraTowerAsymptote` /
                                 `TowerFixedPoint`
