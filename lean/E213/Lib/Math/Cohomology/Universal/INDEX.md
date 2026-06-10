# `Cohomology/Universal/` — Universal cup-product propositions

Universal-AW (Alexander-Whitney) propositions in the cup-product
ring.  Each `Prop<N>` is a numbered universal-form theorem
catalogued in `research-notes/frontiers/G35`.

## Files (8)

### Core
  - `Core.lean`      — Universal cup-ring scaffolding
  - `Prop.lean`      — Prop base type

### Universal propositions (G35 series)
  - `Prop31.lean`    — Prop 31: pattern_eq
  - `Prop41.lean`    — Prop 41
  - `Prop42.lean`    — Prop 42
  - `Prop51.lean`    — Prop 51
  - `Prop52.lean`    — Prop 52
  - `Prop53.lean`    — Prop 53

## Where to add new files

  - New universal proposition  → `Prop<N>.lean`  (match G35 catalog
                                  numbering)
  - Core extension             → `Core.lean`

## Companion clusters

  - `Cohomology/Cup/`     — strict cup product
  - `Cohomology/CupAW/`   — Alexander-Whitney cup
  - `HodgeConjecture/Pairing/` — HIT + HR (consumes universal AW)
