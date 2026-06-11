# `CayleyDickson/Levels/` — CD level instances (Cayley / Sedenion / Pathion / Trig.)

Level-by-level Cayley-Dickson instances above ZI / Lipschitz:
Cayley (octonions, level 4), Sedenion (level 5), Pathion (level 6),
Trigintaduonion (level 7).  Each comes in a Lite + Heavy variant
plus order-4 monopoly results.

## Files (11)

### Cayley (level 4 — octonion-like)
  - `Cayley.lean`               — Cayley structure (lite)
  - `CayleyHeavy.lean`          — full Cayley level results
  - `CayleyOrder4Monopoly.lean` — order-4 monopoly at Cayley

### Sedenion (level 5)
  - `Sedenion.lean`               — Sedenion structure (lite)
  - `SedenionHeavy.lean`          — full Sedenion results
  - `SedenionOrder4Monopoly.lean` — order-4 monopoly at Sedenion

### Pathion (level 6)
  - `Pathion.lean`           — Pathion structure (lite)
  - `PathionHeavy.lean`      — full Pathion results

### Trigintaduonion (level 7)
  - `Trigintaduonion.lean`           — Trigintaduonion structure
  - `TrigintaduoionionHeavy.lean`    — full Trigintaduonion results

## Pattern

Each level follows:
  - `<Level>.lean`              — lite (base structure + axioms)
  - `<Level>Heavy.lean`         — full proofs (long arithmetic)
  - `<Level>Order4Monopoly.lean`— order-4 monopoly (where applicable)
  - `SedenionZeroDivisor.lean` — sedenion zero divisors — the composition boundary made concrete

## Companion clusters

  - `CayleyDickson/Tower/`     — generic tower machinery (consumes
                                  these levels)
  - `CayleyDickson/Integer/`   — ZI / ZOmega / Hurwitz baselines

## Where to add new files

  - Higher level (8: Sexagintaquatronion?) → follow `<Level>{,Heavy,
    Order4Monopoly}.lean` pattern
  - Level-specific lemma          → `<Level><lemma>.lean`
