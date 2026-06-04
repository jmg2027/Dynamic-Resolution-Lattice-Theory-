import E213.Lib.Math.Cauchy.WronskianDepth

/-!
# φ and π are the two faces of the unit — sign and magnitude

The `det = ±1` unit floor (`WronskianDepth.unit_faces_opposite_depth`) has *names*: φ and π.

  - **φ is the `det = −1` sign face.**  The golden/Fibonacci recurrence `s(n+2) = s(n+1) + s(n)` is
    exactly `p = 1, q = −1`, so its companion has `det = −1` and `disc = 1 − 4·(−1) = 5` — the golden
    discriminant (`NS + NT`), the hyperbolic pole.  Its Cassini cross-determinant is the classical
    **Cassini identity** `F(n+2)F(n) − F(n+1)² = (−1)^{n+1}`: period-2, sign-flipping, and (with
    nonzero seed) of **no finite depth** — the additively-maximal sign-unit.  So the famous Cassini
    identity *is* the `det = −1` face, and φ is its pole.
  - **π is the `det = +1` magnitude face** (the rotation/elliptic side).  The elliptic generators
    `S` (order 4), `U` (order 6) have `det = +1`, `disc < 0`, conserved Cassini, **periodic** orbits
    — the additively-trivial magnitude-unit, realised at *rational* rotation angles (roots of unity).
    π is the limit of that face at an *irrational* angle: still `det = +1` (area-preserving rotation)
    but no finite order — where the periodic floor fails and the continued fraction goes
    non-holonomic.

So φ and π are not two unrelated constants: they are the **two faces of the single unit** `1 = NS −
NT`, read at opposite discriminant signs — φ the sign face (`det = −1`, `disc = 5 > 0`, hyperbolic,
oscillating Cassini, additively maximal), π the magnitude face (`det = +1`, `disc < 0`, elliptic,
conserved Cassini, additively trivial; the irrational-rotation pole of it).  Squaring the golden
iterator sends `det = −1 ↦ (−1)² = +1` — the sign face squared is the magnitude face (`F² = G =
[[2,1],[1,1]]`, still `disc = 5`).
-/

namespace E213.Lib.Math.Cauchy.GoldenPiFaces

open E213.Lib.Math.Cauchy.DetZeroCollapse (cas cas_period2_neg_unit)
open E213.Lib.Math.Cauchy.WronskianDepth (cas_neg_unit_no_finite_depth)
open E213.Lib.Math.Cauchy.EllipticPeriodicTier (comp comp_det comp_disc)
open E213.Lib.Math.NumberSystems.Real213.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ)

/-- ★★ **The golden iterator is the `det = −1` sign face at the golden discriminant `5`.**
    `comp 1 (-1)` (the Fibonacci companion, `x² − x − 1`) has `disc = 5` (hyperbolic, `= NS + NT`)
    and `det = −1` (the sign face). -/
theorem golden_companion_sign_face :
    Mat2.disc (comp 1 (-1)) = 5 ∧ Mat2.det (comp 1 (-1)) = -1 :=
  ⟨(comp_disc 1 (-1)).trans (by decide), comp_det 1 (-1)⟩

/-- ★★★ **φ's Cassini identity is the `det = −1` period-2 oscillation.**  Any golden/Fibonacci
    orbit `s(n+2) = s(n+1) + s(n)` has period-2 Cassini (`cas s (n+2) = cas s n`) — the classical
    `F(n+2)F(n) − F(n+1)² = (−1)^{n+1}`. -/
theorem golden_cassini_period2 (s : Nat → Int) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n) :
    ∀ n, cas s (n + 2) = cas s n := by
  apply cas_period2_neg_unit 1 s
  intro n; show s (n + 2) = 1 * s (n + 1) - (-1) * s n
  rw [hrec n]; ring_intZ

/-- ★★★ **φ's Cassini has no finite depth — the additively-maximal sign-unit.**  A golden orbit
    with nonzero initial Cassini (`W₀ ≠ 0`, e.g. Fibonacci with `W₀ = ±1`) has a Cassini sequence
    of *no* finite difference-depth: the pure period-2 oscillation `(−1)^n`. -/
theorem golden_cassini_no_finite_depth (s : Nat → Int) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (h0 : cas s 0 ≠ 0) : ¬ ∃ d, polyDepthZ d (cas s) := by
  apply cas_neg_unit_no_finite_depth 1 s ?_ h0
  intro n; show s (n + 2) = 1 * s (n + 1) - (-1) * s n
  rw [hrec n]; ring_intZ

end E213.Lib.Math.Cauchy.GoldenPiFaces
