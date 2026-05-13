# `Lib/Physics/Atomic/IE/` — atomic ionization energies

Atomic ionization-energy derivations across the periodic table.
Hydrogenic baseline + period-by-period scaling + Hund penalty.

## Files (15)

### Theoretical scaffolding
  - `Hydrogenic.lean`         — Z²·R∞ hydrogenic IE baseline
  - `HundPenalty.lean`        — Hund's rule penalty term
  - `IonizationEnergies.lean` — general IE formula combinator

### Element-by-element (Period 1–4)
  - `HydrogenPPM.lean`        — H IE at ppm precision
  - `HeliumPPM.lean`          — He IE at ppm precision
  - `Lithium.lean`            — Li (Period 2 head)
  - `Beryllium.lean`          — Be
  - `Boron.lean`              — B
  - `CNOFNe.lean`             — C, N, O, F, Ne (Period 2 tail)
  - `SecondRow.lean`          — Period 2 cumulative

### Periodic structure
  - `Period3.lean`            — Period 3 (Na–Ar)
  - `Period4.lean`            — Period 4 (K–Kr)
  - `PeriodicTable.lean`      — table-level structure
  - `PeriodClosures.lean`     — per-period closure relations

### Capstone
  - `Capstone.lean`           — IE master result

## Top-level

  - `IE.lean` aggregator

## Where to add new files

  - New element            → `<Element>.lean` (alphabetic order
                              within period)
  - Period extension       → `Period<N>.lean`
  - New formula correction → `<correction-name>.lean`
  - Closure / capstone     → match `PeriodClosures` / `Capstone`
