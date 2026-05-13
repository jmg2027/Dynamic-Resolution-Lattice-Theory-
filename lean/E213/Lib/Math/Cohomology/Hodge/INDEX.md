# `Cohomology/Hodge/` — Hodge star + Δ⁴ involution

Hodge star operator + Δ-involution structural propositions on the
213 cohomology complex.

## Files (9)

### Hodge / Delta core
  - `Star.lean`             — Hodge `*` operator
  - `Delta.lean`             — Δ-operator (boundary / cohomology)
  - `Involution.lean`        — Δ-involution property
  - `InvolutionCapstone.lean`— Δ-involution capstone

### Propositions (G35 catalog)
  - `Prop.lean`              — Prop base
  - `Prop50.lean`            — Prop 50
  - `Prop52.lean`            — Prop 52
  - `Prop53.lean`            — Prop 53
  - `Prop54.lean`            — Prop 54

## Where to add new files

  - New Prop in series       → `Prop<N>.lean`
  - Hodge-star refinement    → `Star*` / `Star<refinement>.lean`
  - Δ-operator extension     → `Delta*` / `Involution*`

## Companion clusters

  - `Cohomology/Cup/`        — strict cup product (Δ-related)
  - `Cohomology/CupAW/`      — Alexander-Whitney cup
  - `HodgeConjecture/Pairing/` — HIT + HR pairings
