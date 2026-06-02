import E213.Lib.Math.CassiniUnimodular
import E213.Lib.Math.Cauchy.NewtonGregory

/-!
# Cauchy.CassiniDepthFloor — a conserved (`q = 1`, `SL₂`) orbit sits at depth-0 Cassini

`CassiniUnimodular.det_step` showed the Cassini determinant of any 2nd-order `Int` recurrence
`s(n+2) = p·s(n+1) − q·s(n)` multiplies by `q` each step.  When `q = 1` (the shift is in `SL₂`,
e.g. the golden/Lucas/Pell orbit) the determinant is **conserved** — a *constant* sequence —
hence sits at **divergence depth 0** (`polyDepthZ 0`).

This is the *sufficiency* direction `q = 1 ⟹ depth 0`, the structural floor behind
`DepthResidueFloor.floor_polyDepth0` (the φ/`W` instance).  Honest scope:

  * only `q = 1` is covered — **not** all of unimodular `|q| = 1`: the `q = −1` (period-2) case
    *alternates* (`det_period2_alternates`), so it is depth-0 only when `det s 0 = 0`, otherwise
    genuinely non-constant.  The floor is the `SL₂` (`q = 1`) case, a proper subset of unimodular;
  * this is one-directional — the **converse** (depth-0 Cassini ⟹ `q = 1`) is *false* without a
    non-degeneracy hypothesis (`det s 0 = 0` gives `det s n = qⁿ·0 = 0`, constant for *every*
    `q`), so it is not a biconditional;
  * the reading "the e/ζ(2)/ζ(3) divergence ladder is the *degree of departure* from this `q = 1`
    floor (each rung an `n`-dependent-coefficient drift from the constant-coefficient shift)" is a
    **conjectural interpretation**, NOT formalized here — this file only proves `q = 1 ⟹ depth 0`.
-/

namespace E213.Lib.Math.Cauchy.CassiniDepthFloor

open E213.Lib.Math.CassiniUnimodular (det det_step)
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ isConstZ)
open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Lib.Math.Mobius213.Px.CharPolySelf (L_rec)

/-- ★★★ **A conserved (`q = 1`) orbit's Cassini sits at depth 0.**  For any 2nd-order `Int`
    recurrence with shift determinant `q = 1` (`s(n+2) = p·s(n+1) − 1·s(n)`), the Cassini
    determinant `det s` is *constant* (`det_step` with `q = 1` gives `det s (n+1) = det s n`),
    hence `polyDepthZ 0 (det s)`: the `SL₂` orbit is the **divergence-ladder floor**.  (Sufficiency
    only — `q = 1 ⟹ depth 0`; the converse fails for degenerate `det s 0 = 0`.) -/
theorem cassini_conserved_depth0 (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) :
    polyDepthZ 0 (det s) := by
  show ∀ n, det s n = det s 0
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [det_step p 1 s hrec k, Int.one_mul]; exact ih

/-- ★★ **The golden/Lucas Cassini is a depth-0 floor.**  The `L`-orbit (`L(n+2) = 3·L(n+1) −
    1·L(n)`, shift `[[2,1],[1,1]]`, `det = q = 1`) has a *constant* Cassini (`= d = 5`), hence
    `polyDepthZ 0 (det L)` — an instance of `cassini_conserved_depth0`. -/
theorem golden_cassini_depth0 : polyDepthZ 0 (det L) :=
  cassini_conserved_depth0 3 L (fun n => by rw [Int.one_mul]; exact L_rec n)

/-- ★★ **`q = 1` ⟹ depth 0 (the `SL₂` Cassini floor).**  Bundle of the *sufficiency*: every
    `q = 1` (det-of-shift `= 1`, `SL₂`) 2nd-order orbit has a constant Cassini at depth 0
    (`cassini_conserved_depth0`), and the golden/Lucas orbit is such a floor
    (`golden_cassini_depth0`, `det L = d = 5`).  One-directional — **not** a biconditional, and
    the `SL₂` (`q = 1`) floor is a proper subset of unimodular (`q = −1` period-2 alternates). -/
theorem sl2_cassini_floor :
    (∀ (p : Int) (s : Nat → Int), (∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) →
        polyDepthZ 0 (det s))
    ∧ polyDepthZ 0 (det L) :=
  ⟨cassini_conserved_depth0, golden_cassini_depth0⟩

end E213.Lib.Math.Cauchy.CassiniDepthFloor
