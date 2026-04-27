import E213.Physics.Phase2.Origin
import E213.Physics.Phase2.Shape
import E213.Physics.Phase2.Existence
import E213.Physics.Phase2.Pairs
import E213.Physics.Phase2.Time
import E213.Physics.Phase2.Space
import E213.Physics.Phase2.Observable
import E213.Physics.Phase2.Force
import E213.Physics.Phase2.Edges
import E213.Physics.Phase2.Lens
import E213.Physics.Phase2.Capstone
import E213.Physics.Phase2.Phase1Bridge
import E213.Physics.Phase2.Falsifier

/-!
# E213.Physics.Phase2 — root entry

Phase 2 single import entry point.  Includes all 13 submodules.

## Modules

  * `Origin`        — d=5 unique (Atomicity forced)
  * `Shape`         — 5 vertex, (3,2), 10 pairs
  * `Existence`     — Vertex := Fin 5 + block classification
  * `Pairs`         — AA(3) + BB(1) + AB(6) = 10
  * `Time`          — NT=2 → 2^n dyadic (math track bridge)
  * `Space`         — NS=3 → 3^n ternary, NT/NS asymmetry
  * `Observable`    — 9 axiom-level measurable integers
  * `Force`         — 3 channels = 3 force candidates
  * `Edges`         — c=2 doubling, b_1 = 8 = NS²-1
  * `Lens`          — Hypervisor explicit Lens (parityLens)
  * `Capstone`      — 26-conjunct single synthesis
  * `Phase1Bridge`  — Phase 2 ↔ Phase 1 arithmetic identity (0 axioms)
  * `Falsifier`    — CLAUDE.md criterion (2) falsifiable propositions

## Guarantees

All 0 sorry.  ≤ propext + Quot.sound (Lean 4 core only).
Most are *completely axiom-free* (rfl + decide).

## Operating principles

CLAUDE.md: Do not use "observer/structure/relation/space/perception" words
in axiom descriptions.  Only "primitive distinction".  Everything else is
explicitly output from Lens.

`Phase2/AUDIT.md` — cross-audit against the math track (extreme rigor):
**No Phase 2 violations**.  App/Simplex pattern preserved.
-/
