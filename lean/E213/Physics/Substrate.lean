import E213.Physics.Substrate.Origin
import E213.Physics.Substrate.Shape
import E213.Physics.Substrate.Existence
import E213.Physics.Substrate.Pairs
import E213.Physics.Substrate.Time
import E213.Physics.Substrate.Space
import E213.Physics.Substrate.Observable
import E213.Physics.Substrate.Force
import E213.Physics.Substrate.Edges
import E213.Physics.Substrate.Lens
import E213.Physics.Substrate.Capstone
import E213.Physics.Substrate.Phase1Bridge
import E213.Physics.Substrate.Falsifier

/-!
# `E213.Physics.Substrate` — substrate-genesis cluster

Single-import entry point for the substrate-genesis cluster
(formerly "Phase 2" in earlier session naming).

## Modules

  * `Origin`        — d=5 unique (Atomicity forced)
  * `Shape`         — 5 vertex, (3,2), 10 pairs
  * `Existence`     — Vertex := Fin 5 + block classification
  * `Pairs`         — AA(3) + BB(1) + AB(6) = 10
  * `Time`          — NT=2 → 2^n dyadic (math track bridge)
  * `Space`         — NS=3 → 3^n ternary, NT/NS asymmetry
  * `Observable`    — 9 framework-level measurable integers
  * `Force`         — 3 channels = 3 force candidates
  * `Edges`         — c=2 doubling, b_1 = 8 = NS²-1
  * `Lens`          — Hypervisor explicit Lens (parityLens)
  * `Capstone`      — 26-conjunct single synthesis
  * `Phase1Bridge`  — substrate ↔ Phase-1 arithmetic identity
  * `Falsifier`     — CLAUDE.md criterion (2) falsifiable propositions

## Guarantees

All 0 sorry.  Most are completely axiom-free (rfl + decide);
the rest stay within Lean 4 core (≤ propext + Quot.sound).

## Operating principles

Per CLAUDE.md: do not use "observer / structure / relation / space /
perception" words in framework-level descriptions.  Only "primitive
distinction"; everything else is explicit Lens output.
-/
