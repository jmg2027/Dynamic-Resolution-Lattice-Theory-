-- Umbrella module for `E213.Lib.Math.Mobius213.Px` — symmetry species
-- catalog of P(x), P-orbit closure programme, and related structure.

-- 36-species catalog backbone
import E213.Lib.Math.Mobius213.Px.SymmetrySpecies
import E213.Lib.Math.Mobius213.Px.OpenSpeciesClosure
import E213.Lib.Math.Mobius213.Px.DenomInvariantFamily
import E213.Lib.Math.Mobius213.Px.IterationSpecies
import E213.Lib.Math.Mobius213.Px.ExtendedSpecies
import E213.Lib.Math.Mobius213.Px.AxisGroupCount
import E213.Lib.Math.Mobius213.Px.DecompositionCatalog
import E213.Lib.Math.Mobius213.Px.SyntacticCatalog
import E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock
import E213.Lib.Math.Mobius213.Px.NaturalnessClosure
import E213.Lib.Math.Mobius213.Px.TripartiteK213
import E213.Lib.Math.Mobius213.Px.ModPPeriods
import E213.Lib.Math.Mobius213.Px.POrbitClosure

-- P-orbit closure programme (11-phase marathon)
import E213.Lib.Math.Mobius213.Px.CharPolySelf
import E213.Lib.Math.Mobius213.Px.POrbitRing
import E213.Lib.Math.Mobius213.Px.PeriodDepthBounds
import E213.Lib.Math.Mobius213.Px.CrossProductAxes
import E213.Lib.Math.Mobius213.Px.POrbitDepth
import E213.Lib.Math.Mobius213.Px.CassiniInduction
import E213.Lib.Math.Mobius213.Px.PnFibonacci
import E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal
import E213.Lib.Math.Mobius213.Px.QFibIdentity
import E213.Lib.Math.Mobius213.Px.CassiniUniversal
import E213.Lib.Math.Mobius213.Px.FibCassini
import E213.Lib.Math.Mobius213.Px.LModP
import E213.Lib.Math.Mobius213.Px.PeriodReciprocity

/-!
# `E213.Lib.Math.Mobius213.Px` — umbrella

Single-import entry point for the Möbius P symmetry species
catalog and the P-orbit closure programme.

## Organisation

  · **§1 — 36-species catalog** (13 modules): the original Px
    catalog up to and including the original `POrbitClosure`
    sharpening of the naturalness boundary.
  · **§2 — Closure marathon** (9 modules): the structural
    closure of P-orbit theory.
      - `CharPolySelf`        — P self-reference via L-values
      - `POrbitRing`          — inductive ring closure
      - `PeriodDepthBounds`   — primes 41–97 + depth tags
      - `CrossProductAxes`    — Bipartite × Tripartite × P-orbit
      - `POrbitDepth`         — inductive depth predicate
      - `CassiniInduction`    — Cassini at n = 0..9
      - `PnFibonacci`         — P^n entries = consecutive Fibonacci
      - `LModP`               — L mod p cycle closure
      - `PeriodReciprocity`   — T_p · q = p ± 1 via Legendre(5, p)

## Companion module

  · `E213.Theory.Atomicity.OrbitForcing` — the static-to-dynamic
    forcing lift, now the 8th file in the `Theory.Atomicity`
    cluster.  Not under `Px/` because it belongs to the Theory
    ring rather than Lib.Math.Mobius213.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Mobius213.Px
python3 ../tools/scan_axioms.py E213.Lib.Math.Mobius213.Px
```

## Cross-references

  · `theory/math/mobius213_p_orbit_closure.md` — chapter
  · `theory/essays/p_orbit_closure_master.md` — 11-phase essay
-/
