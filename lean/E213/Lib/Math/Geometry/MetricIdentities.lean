import E213.Lib.Math.Geometry.StewartTheorem
import E213.Meta.Int213.Order

/-!
# Classical Euclidean metric identities (∅-axiom)

Companion to `StewartTheorem.lean`, reusing its integer squared-distance `sq`.  Three more
named results that reduce to polynomial identities over `ℤ`:

  * `british_flag` — for a rectangle `ABCD` (adjacent sides `u ⊥ v`) and any point `P`,
    `PA² + PC² = PB² + PD²`.
  * `parallelogram_law` — `AC² + BD² = 2·AB² + 2·AD²` (sum of squared diagonals = twice the
    sum of squared sides), no perpendicularity needed.
  * `pythagoras` — right angle at `B` (legs `u ⊥ v`) gives `AC² = AB² + BC²`.

The rectangle/right-angle cases carry a perpendicularity hypothesis `u·v = 0`; the residual
`2·(u·v)` term is killed by it via `eq_of_sub_eq_zero`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Geometry.MetricIdentities

open E213.Lib.Math.Geometry.StewartTheorem (Pt sq)
open E213.Meta.Int213.PolyIntM
open E213.Meta.Int213.PolyIntM (mul_zeroZ)
open E213.Meta.Int213 (zero_add add_comm)
open E213.Meta.Int213.Order (eq_of_sub_eq_zero sub_self_zero)

/-- ★★★ **British flag theorem**: for a rectangle with corner `A` and perpendicular adjacent
    side-vectors `u = (ux,uy)`, `v = (vx,vy)` (so `B = A+u`, `D = A+v`, `C = A+u+v`), and any
    point `P`, the two squared-diagonal-corner sums are equal: `PA² + PC² = PB² + PD²`. -/
theorem british_flag (A P : Pt) (ux uy vx vy : Int) (hperp : ux * vx + uy * vy = 0) :
    sq P A + sq P (A.1 + ux + vx, A.2 + uy + vy)
      = sq P (A.1 + ux, A.2 + uy) + sq P (A.1 + vx, A.2 + vy) := by
  refine eq_of_sub_eq_zero ?_
  -- the difference equals `2·(u·v)`, which is `0`
  have key : sq P A + sq P (A.1 + ux + vx, A.2 + uy + vy)
        - (sq P (A.1 + ux, A.2 + uy) + sq P (A.1 + vx, A.2 + vy))
      = 2 * (ux * vx + uy * vy) := by
    show (P.1 - A.1) * (P.1 - A.1) + (P.2 - A.2) * (P.2 - A.2)
        + ((P.1 - (A.1 + ux + vx)) * (P.1 - (A.1 + ux + vx))
            + (P.2 - (A.2 + uy + vy)) * (P.2 - (A.2 + uy + vy)))
        - ((P.1 - (A.1 + ux)) * (P.1 - (A.1 + ux)) + (P.2 - (A.2 + uy)) * (P.2 - (A.2 + uy))
            + ((P.1 - (A.1 + vx)) * (P.1 - (A.1 + vx)) + (P.2 - (A.2 + vy)) * (P.2 - (A.2 + vy))))
      = 2 * (ux * vx + uy * vy)
    ring_intZ
  rw [key, hperp]; decide

/-- ★★★ **Parallelogram law**: with `B = A+u`, `D = A+v`, `C = A+u+v`, the sum of the squared
    diagonals equals twice the sum of the squared sides: `AC² + BD² = 2·AB² + 2·AD²`.
    No perpendicularity required — a free `ring_intZ` identity. -/
theorem parallelogram_law (A : Pt) (ux uy vx vy : Int) :
    sq (A.1 + ux + vx, A.2 + uy + vy) A + sq (A.1 + ux, A.2 + uy) (A.1 + vx, A.2 + vy)
      = 2 * sq (A.1 + ux, A.2 + uy) A + 2 * sq (A.1 + vx, A.2 + vy) A := by
  show ((A.1 + ux + vx) - A.1) * ((A.1 + ux + vx) - A.1)
      + ((A.2 + uy + vy) - A.2) * ((A.2 + uy + vy) - A.2)
      + (((A.1 + ux) - (A.1 + vx)) * ((A.1 + ux) - (A.1 + vx))
          + ((A.2 + uy) - (A.2 + vy)) * ((A.2 + uy) - (A.2 + vy)))
    = 2 * (((A.1 + ux) - A.1) * ((A.1 + ux) - A.1) + ((A.2 + uy) - A.2) * ((A.2 + uy) - A.2))
      + 2 * (((A.1 + vx) - A.1) * ((A.1 + vx) - A.1) + ((A.2 + vy) - A.2) * ((A.2 + vy) - A.2))
  ring_intZ

/-- ★★★ **Pythagorean theorem**: a right angle at `B` (legs `u = A−B`, `v = C−B` with `u ⊥ v`)
    gives `AC² = AB² + BC²`.  Here `A = B+u`, `C = B+v`, `u·v = 0`. -/
theorem pythagoras (B : Pt) (ux uy vx vy : Int) (hperp : ux * vx + uy * vy = 0) :
    sq (B.1 + ux, B.2 + uy) (B.1 + vx, B.2 + vy)
      = sq (B.1 + ux, B.2 + uy) B + sq (B.1 + vx, B.2 + vy) B := by
  refine eq_of_sub_eq_zero ?_
  have key : sq (B.1 + ux, B.2 + uy) (B.1 + vx, B.2 + vy)
        - (sq (B.1 + ux, B.2 + uy) B + sq (B.1 + vx, B.2 + vy) B)
      = (-2) * (ux * vx + uy * vy) := by
    show ((B.1 + ux) - (B.1 + vx)) * ((B.1 + ux) - (B.1 + vx))
        + ((B.2 + uy) - (B.2 + vy)) * ((B.2 + uy) - (B.2 + vy))
        - (((B.1 + ux) - B.1) * ((B.1 + ux) - B.1) + ((B.2 + uy) - B.2) * ((B.2 + uy) - B.2)
            + (((B.1 + vx) - B.1) * ((B.1 + vx) - B.1) + ((B.2 + vy) - B.2) * ((B.2 + vy) - B.2)))
      = (-2) * (ux * vx + uy * vy)
    ring_intZ
  rw [key, hperp]; decide

/-- Smoke: `3-4-5` right triangle `B=(0,0)`, `A=(3,0)`, `C=(0,4)`: `AC²=25 = 9 + 16`. -/
theorem pythagoras_smoke :
    sq (3, 0) (0, 4) = sq (3, 0) (0, 0) + sq (0, 4) (0, 0) := by decide

/-- ★★★ **Leibniz centroid formula** (the `n = 3` moment / variance-decomposition identity):
    for the centroid `G` of triangle `ABC` (`3·G = A + B + C`) and any point `P`,

      `PA² + PB² + PC² = GA² + GB² + GC² + 3·PG²`.

    The cross term `−2·(P−G)·(A+B+C−3G)` vanishes by the centroid condition — this is exactly
    the parallel-axis theorem / `Var(X) = E[X²] − E[X]²` decomposition in disguise. -/
theorem leibniz_centroid (A B C G P : Pt)
    (h1 : 3 * G.1 = A.1 + B.1 + C.1) (h2 : 3 * G.2 = A.2 + B.2 + C.2) :
    sq P A + sq P B + sq P C = sq G A + sq G B + sq G C + 3 * sq P G := by
  have key : sq P A + sq P B + sq P C
      = sq G A + sq G B + sq G C + 3 * sq P G
          + (-2) * ((P.1 - G.1) * ((A.1 + B.1 + C.1) - 3 * G.1)
              + (P.2 - G.2) * ((A.2 + B.2 + C.2) - 3 * G.2)) := by
    show (P.1-A.1)*(P.1-A.1)+(P.2-A.2)*(P.2-A.2)
        + ((P.1-B.1)*(P.1-B.1)+(P.2-B.2)*(P.2-B.2))
        + ((P.1-C.1)*(P.1-C.1)+(P.2-C.2)*(P.2-C.2))
      = (G.1-A.1)*(G.1-A.1)+(G.2-A.2)*(G.2-A.2)
            + ((G.1-B.1)*(G.1-B.1)+(G.2-B.2)*(G.2-B.2))
            + ((G.1-C.1)*(G.1-C.1)+(G.2-C.2)*(G.2-C.2))
            + 3*((P.1-G.1)*(P.1-G.1)+(P.2-G.2)*(P.2-G.2))
        + (-2) * ((P.1 - G.1) * ((A.1 + B.1 + C.1) - 3 * G.1)
            + (P.2 - G.2) * ((A.2 + B.2 + C.2) - 3 * G.2))
    ring_intZ
  have z1 : (A.1 + B.1 + C.1) - 3 * G.1 = 0 := by rw [← h1]; exact sub_self_zero _
  have z2 : (A.2 + B.2 + C.2) - 3 * G.2 = 0 := by rw [← h2]; exact sub_self_zero _
  rw [z1, z2, mul_zeroZ, mul_zeroZ, zero_add, mul_zeroZ] at key
  rw [key]
  exact (add_comm _ 0).trans (zero_add _)

/-- Smoke: `A=(0,0)`, `B=(6,0)`, `C=(0,6)`, centroid `G=(2,2)`, `P=(0,0)`.
    `PA²+PB²+PC² = 0+36+36 = 72`; `GA²+GB²+GC² = 8+20+20 = 48`; `3·PG² = 3·8 = 24`; `48+24=72`. -/
theorem leibniz_smoke :
    sq (0, 0) (0, 0) + sq (0, 0) (6, 0) + sq (0, 0) (0, 6)
      = sq (2, 2) (0, 0) + sq (2, 2) (6, 0) + sq (2, 2) (0, 6) + 3 * sq (0, 0) (2, 2) := by decide

end E213.Lib.Math.Geometry.MetricIdentities
