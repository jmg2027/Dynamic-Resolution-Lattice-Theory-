import E213.Lib.Physics.AtomicBase.Origin
import E213.Lib.Physics.AtomicBase.Shape
import E213.Lib.Physics.AtomicBase.Existence
import E213.Lib.Physics.AtomicBase.Pairs
import E213.Lib.Physics.AtomicBase.Time
import E213.Lib.Physics.AtomicBase.Space
import E213.Lib.Physics.AtomicBase.Observable
import E213.Lib.Physics.AtomicBase.Force
import E213.Lib.Physics.AtomicBase.Edges
import E213.Lib.Physics.AtomicBase.Lens
import E213.Lib.Physics.AtomicBase.Capstone
import E213.Lib.Physics.AtomicBase.Phase1Bridge
import E213.Lib.Physics.AtomicBase.Falsifier

/-!
# `E213.Lib.Physics.AtomicBase` — atomic-base genesis cluster

Single-import entry point for the atomic-primitive readings.
Renamed from "Substrate" (2026-05-20) — the previous naming
imported a substrate / superstructure framing inconsistent
with §8.1's no-exterior principle.  This cluster records what
Raw reads under the atomicity-Lens at the most primitive level
(d, NS, NT, c and direct consequences); other clusters
elaborate further Lens readings of the same residue.

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
  * `Lens`          — explicit Lens (parityLens)
  * `Capstone`      — 26-conjunct single synthesis
  * `Phase1Bridge`  — atomic-base ↔ Phase-1 arithmetic identity
  * `Falsifier`     — CLAUDE.md criterion (2) falsifiable propositions

## Guarantees

All 0 sorry.  Most are completely axiom-free (rfl + decide);
the rest stay within Lean 4 core (≤ propext + Quot.sound).

## Operating principles

Per CLAUDE.md: do not use "observer / structure / relation / space /
perception" words in framework-level descriptions.  Only "primitive
distinction"; everything else is explicit Lens output.
-/
