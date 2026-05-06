# Periodic Table 213 — Narrative

The standard chemistry periodic table = quantum numbers (n, l, m, s) + Madelung
filling assumption.  DRLT 213 represents *all of these via atomic primitives*.

## Key findings

All noble gases (period closures) are atomic:

  Period 1 (Z=2)   He = NT
  Period 2 (Z=10)  Ne = d·NT
  Period 3 (Z=18)  Ar = 2·NS²
  Period 4 (Z=36)  Kr = (NS·NT)²    ★ square of same 6=NS·NT
  Period 5 (Z=54)  Xe = 2·NS³
  Period 6 (Z=86)  Rn = 2·NS³ + NT^d
  Period 7 (Z=118) Og = 2·NS³ + 2·NT^d
  Period 8 (Z=168) [prediction] = HO magic 7 = n(n+1)(n+2)/3

## IE precision

  H   4.3 ppb formal Lean
  He  138 ppm  (4·R · (1/NT - 2α_GUT))
  Li  113 ppm  (R · 25/64 · P(x))
  Be  493 ppm  (P(x/2))
  B   1046 ppm

P(x) = (1+2x)/(1+x), x = α_GUT·NS/d atomic.
The same closed propagator applies to m_p, m_H, Ω_Λ, and IE.

## Hund's rule atomic

  ε_pair = R · NS/(NS²-1) = R · α_3 · NS = R · 3/8

  The same α_3 = 1/8 is strong coupling + Hund penalty.

## Usage

```lean
import E213.Lib.Physics.Library.CompletePeriodicTable
```

## Formal guarantees

  - All 113 elements + 5 super-heavy atomically verified
  - Period closures 7 + 1 prediction all atomic
  - Hund's rule atomic Lean theorem (0 axioms)
  - No borrowing of standard quantum numbers

## References

  blueprints/physics/01_atomic_physics_213.md
  catalogs/periodic-table.md
  lean/E213.Lib.Physics.Library/CompletePeriodicTable.lean
