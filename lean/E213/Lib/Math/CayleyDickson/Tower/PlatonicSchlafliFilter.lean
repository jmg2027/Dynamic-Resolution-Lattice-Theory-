import E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree
import E213.Lib.Math.CayleyDickson.Tower.IcosianClassStructure

/-!
# Why *exactly three*?  The spherical (Platonic) filter

`CyclotomicTraceDegree` showed the quadratic-trace orders (the 4D /
quaternion layer, `φ(n) = 4`) are `{5, 8, 10, 12}` — four orders.  But
there are only **three** exceptional rungs `E₆, E₇, E₈`.  What cuts four
(or infinitely many rotation orders) down to three?

**The spherical condition** `1/p + 1/q + 1/r > 1` — finite ⇒ positive
curvature ⇒ a Platonic solid.  This is the last filter, and it is sharp:

  * **Schläfli census.**  Regular polytopes `{p,q}` (`p`-gon faces, `q`
    at a vertex) close up on the sphere iff `1/p + 1/q > 1/2`, i.e.
    `(p−2)(q−2) < 4`.  For `p,q ≥ 3` this is **exactly five** solids:
    `{3,3}, {3,4}, {4,3}, {3,5}, {5,3}` — tetra, octa, cube, icosa,
    dodeca.
  * **Dual collapse.**  `{3,4}≈{4,3}` (octa/cube) and `{3,5}≈{5,3}`
    (icosa/dodeca) share a rotation group, so the five solids carry
    **three** rotation groups `A₄, S₄, A₅` (orders `12, 24, 60`).
  * **Triangle form.**  Equivalently the `(2,3,n)` triangle group is
    finite iff `1/2 + 1/3 + 1/n > 1` iff `5n+6 > 6n` iff `n < 6`; the
    polyhedral cases `n ∈ {3,4,5}` are tetra/octa/icosa.

So the three exceptional rungs are the three spherical `(2,3,n)`:
`n = 3` (`E₆/2T`), `n = 4` (`E₇/2O`), `n = 5` (`E₈/2I`), with binary
orders `2·|A₄,S₄,A₅| = 24, 48, 120`.  The boundary `(p−2)(q−2) = 4`
(`{4,4}, {3,6}, {6,3}`, i.e. `1/2+1/3+1/6 = 1`) is **Euclidean** — the
affine `Ê` extension, where the tower stops being finite.  And the
triangle indices `{3,4,5} = {NS, NS+1, NS+NT}` are the atomic numbers:
`E₆ = NS`, `E₇ = NS+1`, `E₈ = NS+NT`.

This closes the "why these" chain: `φ(n)` (Phase 17) admits the quadratic
orders into 4D; the spherical condition selects the three with a Platonic
realisation; the seeds (`√NT`, `√(NS+NT)`) are their cyclotomic traces.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.PlatonicSchlafliFilter

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.CayleyDickson.Tower.IcosianClassStructure (fact)

/-- All `(p,q)` pairs with `p,q ≤ 6`, as the search space for `{p,q}`. -/
def schlafliPairs : List (Nat × Nat) :=
  (List.range 7).flatMap (fun p => (List.range 7).map (fun q => (p, q)))

/-- **The five Platonic solids.**  `{p,q}` with `p,q ≥ 3` closes on the
    sphere iff `(p−2)(q−2) < 4`; the solutions are exactly the five
    regular polyhedra. -/
theorem schlafli_platonic_five :
    schlafliPairs.filter (fun pq => 3 ≤ pq.1 && 3 ≤ pq.2 && (pq.1 - 2) * (pq.2 - 2) < 4)
      = [(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)] := by decide

/-- **The Euclidean boundary.**  `(p−2)(q−2) = 4` (i.e. `1/p+1/q = 1/2`)
    gives the three regular plane tilings `{4,4}, {3,6}, {6,3}` — the
    affine `Ê` edge where the finite tower ends. -/
theorem schlafli_euclidean_boundary :
    schlafliPairs.filter (fun pq => 3 ≤ pq.1 && 3 ≤ pq.2 && (pq.1 - 2) * (pq.2 - 2) == 4)
      = [(3, 6), (4, 4), (6, 3)] := by decide

/-- **The `(2,3,n)` triangle filter.**  `1/2 + 1/3 + 1/n > 1` (finite,
    spherical) iff `5n+6 > 6n` iff `n < 6`; the polyhedral range `n ≥ 3`
    gives exactly `{3,4,5}`. -/
theorem spherical_triangle_233n :
    (List.range 13).filter (fun n => 3 ≤ n && 5 * n + 6 > 6 * n) = [3, 4, 5] := by decide

/-- The five solids carry **three** rotation groups `A₄, S₄, A₅` of
    orders `12, 24, 60` (dual pairs collapse); their binary covers have
    orders `24, 48, 120 = (NS+1)!, 2·(NS+1)!, (NS+NT)!`. -/
theorem three_rotation_groups :
    (fact 4 / 2 = 12 ∧ fact 4 = 24 ∧ fact (NS + NT) / 2 = 60)
    ∧ (2 * 12 = 24 ∧ 2 * 24 = 48 ∧ 2 * 60 = 120)
    ∧ (fact (NS + 1) = 24 ∧ 2 * fact (NS + 1) = 48 ∧ fact (NS + NT) = 120) := by decide

/-- The three spherical triangle indices `{3,4,5}` are the atomic
    numbers `{NS, NS+1, NS+NT}`. -/
theorem triangle_indices_atomic :
    (3 = NS) ∧ (4 = NS + 1) ∧ (5 = NS + NT) := by decide

/-- ★★★ **Why exactly three exceptional rungs: the spherical filter.**
    Of the quadratic-trace orders admitted into 4D, the spherical
    condition `1/p+1/q+1/r > 1` selects exactly the Platonic cases: five
    solids `{3,3},{3,4},{4,3},{3,5},{5,3}` collapsing (by duality) to
    three rotation groups `A₄,S₄,A₅`, the `(2,3,n)` triangles `n∈{3,4,5}
    = {NS,NS+1,NS+NT}`, with binary orders `24,48,120`.  The boundary
    `(p−2)(q−2)=4` is Euclidean (the affine edge). -/
theorem why_exactly_three :
    -- five Platonic solids …
    (schlafliPairs.filter (fun pq => 3 ≤ pq.1 && 3 ≤ pq.2 && (pq.1 - 2) * (pq.2 - 2) < 4)
      = [(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)])
    -- … three (2,3,n) triangles n ∈ {3,4,5} = {NS, NS+1, NS+NT} …
    ∧ ((List.range 13).filter (fun n => 3 ≤ n && 5 * n + 6 > 6 * n) = [3, 4, 5])
    ∧ ((3 = NS) ∧ (4 = NS + 1) ∧ (5 = NS + NT))
    -- … three binary covers of orders 24, 48, 120 …
    ∧ (fact (NS + 1) = 24 ∧ 2 * fact (NS + 1) = 48 ∧ fact (NS + NT) = 120)
    -- … and the Euclidean boundary {4,4},{3,6},{6,3} where finiteness ends.
    ∧ (schlafliPairs.filter (fun pq => 3 ≤ pq.1 && 3 ≤ pq.2 && (pq.1 - 2) * (pq.2 - 2) == 4)
        = [(3, 6), (4, 4), (6, 3)]) := by
  refine ⟨schlafli_platonic_five, spherical_triangle_233n, triangle_indices_atomic, ?_,
    schlafli_euclidean_boundary⟩
  exact ⟨by decide, by decide, by decide⟩

end E213.Lib.Math.CayleyDickson.Tower.PlatonicSchlafliFilter
