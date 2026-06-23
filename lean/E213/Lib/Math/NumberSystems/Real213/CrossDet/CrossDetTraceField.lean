import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ParabolicTranslation
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ParabolicSignature
import E213.Meta.Int213.PolyIntMTactic

/-!
# CrossDetTraceField — the cross-determinant's number field *is* the modular trace field

Two trichotomies sit on opposite sides of the cross-determinant story:

  * the **number-field reading** of the cross-determinant's reference forms
    (`EisensteinSignature`, `ParabolicSignature`) — the golden form `m²−mk−k²`
    (disc `+5`, real-quadratic `ℚ(√5)`, a convergent **line**), the parabolic form
    `(m−k)²` (disc `0`, rational, the **cusp**), the Eisenstein norm `a²−ab+b²`
    (disc `−3`, imaginary-quadratic `ℚ(√−3) = ℚ(ω)`, a **curve** / torus);
  * the **trace reading** of the `SL(2,ℤ)` conjugacy faces (`HyperbolicBoost`,
    `ParabolicTranslation`, `UTracePeriodic`) — the golden boost `G = [[2,1],[1,1]]`
    (`tr²−4 = +5`, hyperbolic), the translation `T = [[1,1],[0,1]]` (`tr²−4 = 0`,
    parabolic), the elliptic generator `U = [[0,−1],[1,1]]` (`tr²−4 = −3`, elliptic).

The discriminants `{+5, 0, −3}` agree on both sides.  This file supplies the structural
reason the agreement is forced — the content of "the number-field reading of the cross-determinant" (*the number-field
reading of the cross-determinant*): the bridging object is the **fixed-point form** of a
Möbius map.

`M = [[a,b],[c,d]]` acts as `z ↦ (az+b)/(cz+d)`; its fixed points solve
`c·z² + (d−a)·z − b = 0`, the binary quadratic form `fixForm M = (c, d−a, −b)`.  Its
discriminant is, *as a pure ring identity over `ℤ`*,

  `formDisc (fixForm M) = (d−a)² + 4bc = (a+d)² − 4(ad−bc) = tr(M)² − 4·det(M) = traceDisc M`.

So the number field `ℚ(√D)` in which the cross-determinant's reference lives (`D` = the
form discriminant) coincides with the trace field `tr²−4` of the modular transformation
that the geodesic's monodromy uses, because the reference form is the fixed-point form of
the monodromy matrix.  On the three faces the fixed-point form is the reference form on the
nose:

  * `fixForm G = (1,−1,−1)` — the **golden form**, root `φ`, disc `+5`, hyperbolic, line;
  * `fixForm T = (0,0,−1)`  — degenerate (fixed point at `∞`), disc `0`, parabolic, cusp;
  * `fixForm U = (1,1,1)`   — the **cyclotomic form** `x²+x+1`, root `ω`, disc `−3`,
    elliptic, curve  (the Eisenstein field `ℚ(ω)`; the signature's `eisForm = x²−x+1`,
    root `−ω²`, is the `x ↦ −x`-equivalent representative of the same disc-`−3` field).

The sign of the single number `D = tr²−4` is then **simultaneously** the dial of both
trichotomies — Mingu's "Eisenstein ↦ curve" elliptic conjecture made exact: `D > 0` ⟹ two
real fixed points ⟹ a hyperbolic geodesic (real-quadratic, the **line**); `D = 0` ⟹ one
repeated real fixed point ⟹ parabolic (the rational **cusp**); `D < 0` ⟹ a
complex-conjugate fixed-point pair ⟹ an elliptic point of `ℍ` (imaginary-quadratic, no real
geodesic — the **curve** / torus `ℂ/ℤ[ω]`).

All zero-axiom (`ring_intZ` for the structural identity, `decide` for the instances).
-/

namespace E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetTraceField

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 S U)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicBoost (G)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ParabolicTranslation (T)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature (goldenForm eisForm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ParabolicSignature (parabForm)

/-! ## §1 — the three discriminant readings -/

/-- The discriminant `b² − 4ac` of a binary quadratic form `a·x² + b·xy + c·y²`.  This is
    the *number-field* reading: the form's roots generate `ℚ(√(formDisc a b c))`. -/
def formDisc (a b c : Int) : Int := b * b - 4 * a * c

/-- The trace discriminant `tr(M)² − 4·det(M)` of a `2×2` integer matrix — the discriminant
    of its characteristic polynomial `λ² − tr·λ + det`, the `SL(2,ℤ)` conjugacy invariant
    that selects hyperbolic / parabolic / elliptic. -/
def traceDisc (M : Mat2) : Int :=
  (M.a + M.d) * (M.a + M.d) - 4 * (M.a * M.d - M.b * M.c)

/-- The **fixed-point form** of the Möbius map `z ↦ (az+b)/(cz+d)`: its fixed points solve
    `c·z² + (d−a)·z − b = 0`, the binary form with coefficients `(c, d−a, −b)`. -/
def fixForm (M : Mat2) : Int × Int × Int := (M.c, M.d - M.a, -M.b)

/-! ## §2 — the structural identity: fixed-point-form discriminant = trace discriminant -/

/-- ★★★★ **The cross-determinant's number field is the modular trace field.**  For *every*
    integer matrix `M`, the discriminant of its fixed-point form equals its trace
    discriminant — a pure ring identity over `ℤ`:

      `(d−a)² − 4·c·(−b) = (a+d)² − 4(ad − bc)`,  i.e.  `(d−a)² + 4bc = tr² − 4·det`.

    The number field `ℚ(√D)` the cross-determinant's reference lives in (`D` = the form
    discriminant) is the trace field `tr²−4` of the modular monodromy, because the
    reference form is the fixed-point form of the monodromy matrix. -/
theorem fixForm_disc_eq_traceDisc (M : Mat2) :
    formDisc (fixForm M).1 (fixForm M).2.1 (fixForm M).2.2 = traceDisc M := by
  show (M.d - M.a) * (M.d - M.a) - 4 * M.c * (-M.b)
     = (M.a + M.d) * (M.a + M.d) - 4 * (M.a * M.d - M.b * M.c)
  ring_intZ

/-! ## §2b — the monodromy is an automorph of its fixed-point form -/

/-- Evaluate a binary quadratic form `(A,B,C)` at `(x,y)`: `A·x² + B·xy + C·y²`. -/
def formEval (Q : Int × Int × Int) (x y : Int) : Int :=
  Q.1 * (x * x) + Q.2.1 * (x * y) + Q.2.2 * (y * y)

/-- ★★★★ **The monodromy preserves its fixed-point form, up to `det`.**  Acting on a vector
    by `v ↦ (ax+by, cx+dy)`, the fixed-point form transforms by the determinant:

      `fixForm M (M·v) = det(M) · fixForm M (v)`   (a pure ring identity over `ℤ`).

    So for `M ∈ SL(2,ℤ)` (`det = 1`) the matrix is an **automorph** of its fixed-point form
    — the reference form is the *conserved quantity* of the modular monodromy, exactly as
    the cross-determinant `W` is conserved (`crossDet_step`, multiplier `−q`) on the
    Cassini floor.  The number-field reading is no accident: the geodesic's monodromy holds
    its own fixed-point form invariant, and that form's discriminant is `tr²−4`. -/
theorem fixForm_automorph (M : Mat2) (x y : Int) :
    formEval (fixForm M) (M.a * x + M.b * y) (M.c * x + M.d * y)
      = (M.a * M.d - M.b * M.c) * formEval (fixForm M) x y := by
  show M.c * ((M.a * x + M.b * y) * (M.a * x + M.b * y))
        + (M.d - M.a) * ((M.a * x + M.b * y) * (M.c * x + M.d * y))
        + (-M.b) * ((M.c * x + M.d * y) * (M.c * x + M.d * y))
      = (M.a * M.d - M.b * M.c)
        * (M.c * (x * x) + (M.d - M.a) * (x * y) + (-M.b) * (y * y))
  ring_intZ

/-! ## §3 — the fixed-point forms recover the reference forms on the three faces -/

/-- `fixForm G = (1,−1,−1)` — the **golden form** `m² − mk − k²` (root `φ`). -/
theorem fixForm_G : fixForm G = (1, -1, -1) := by decide

/-- `fixForm T = (0,0,−1)` — degenerate: the fixed point is at `∞` (the cusp). -/
theorem fixForm_T : fixForm T = (0, 0, -1) := by decide

/-- `fixForm U = (1,1,1)` — the **cyclotomic form** `x² + x + 1` (root `ω`, the primitive
    cube root of unity), the disc-`−3` Eisenstein field `ℚ(ω)`. -/
theorem fixForm_U : fixForm U = (1, 1, 1) := by decide

/-- `fixForm S = (1,0,1)` — the **Gaussian form** `x² + 1` (root `i`), disc `−4`, the
    fourth-order CM point.  (The middle rung of the `{2,4,6}` axis on the elliptic side.) -/
theorem fixForm_S : fixForm S = (1, 0, 1) := by decide

/-! ## §4 — the signature reference forms carry exactly these discriminants -/

/-- The golden form is the binary form `1·m² + (−1)·mk + (−1)·k²`. -/
theorem goldenForm_coeffs (m k : Int) :
    goldenForm m k = 1 * (m * m) + (-1) * (m * k) + (-1) * (k * k) := by
  show m * m - m * k - k * k = 1 * (m * m) + (-1) * (m * k) + (-1) * (k * k)
  ring_intZ

/-- The Eisenstein norm form is the binary form `1·a² + (−1)·ab + 1·b²`. -/
theorem eisForm_coeffs (a b : Int) :
    eisForm a b = 1 * (a * a) + (-1) * (a * b) + 1 * (b * b) := by
  show a * a - a * b + b * b = 1 * (a * a) + (-1) * (a * b) + 1 * (b * b)
  ring_intZ

/-- The parabolic form is the binary form `1·m² + (−2)·mk + 1·k²`. -/
theorem parabForm_coeffs (m k : Int) :
    parabForm m k = 1 * (m * m) + (-2) * (m * k) + 1 * (k * k) := by
  show (m - k) * (m - k) = 1 * (m * m) + (-2) * (m * k) + 1 * (k * k)
  ring_intZ

/-- The three signature reference forms have discriminants `+5`, `0`, `−3`. -/
theorem signature_form_discriminants :
    formDisc 1 (-1) (-1) = 5      -- golden:    ℚ(√5),  real-quadratic
    ∧ formDisc 1 (-2) 1 = 0       -- parabolic: ℚ,      degenerate
    ∧ formDisc 1 (-1) 1 = -3 := by -- Eisenstein:ℚ(√−3), imaginary-quadratic
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §5 — the grand unification, and the line/cusp/curve elliptic conjecture -/

/-- ★★★★ **The two trichotomies are one.**  Face by face, the fixed-point form of the
    `SL(2,ℤ)` representative equals the cross-determinant's signature reference form, and
    its discriminant equals the matrix's trace discriminant `tr²−4`:

      * **hyperbolic / golden / line**: `fixForm G = (1,−1,−1)` (golden form),
        `traceDisc G = formDisc(golden) = +5` — real-quadratic `ℚ(√5)`, a convergent line;
      * **parabolic / cusp**: `fixForm T = (0,0,−1)` (fixed point at `∞`),
        `traceDisc T = 0` — the degenerate rational direction, the single cusp;
      * **elliptic / Eisenstein / curve**: `fixForm U = (1,1,1)` (cyclotomic form, root
        `ω`), `traceDisc U = formDisc(eisenstein) = −3` — imaginary-quadratic `ℚ(ω)`, a
        torus / `j=0` elliptic-curve lattice;

    closed by the universal identity `fixForm_disc_eq_traceDisc` (∀ `M`).  The
    cross-determinant's *number-field* reading and the modular *trace-field* reading are the
    same number `D = tr²−4`. -/
theorem crossdet_number_field_is_trace_field :
    -- hyperbolic: the fixed-point form of G is the golden form, disc +5
    (fixForm G = (1, -1, -1) ∧ traceDisc G = 5 ∧ formDisc 1 (-1) (-1) = 5)
    -- parabolic: T fixes ∞, disc 0
    ∧ (fixForm T = (0, 0, -1) ∧ traceDisc T = 0 ∧ formDisc 1 (-2) 1 = 0)
    -- elliptic: the fixed-point form of U is the cyclotomic (Eisenstein) form, disc −3
    ∧ (fixForm U = (1, 1, 1) ∧ traceDisc U = -3 ∧ formDisc 1 (-1) 1 = -3)
    -- the universal reason: fixed-point-form discriminant = trace discriminant, for all M
    ∧ (∀ M : Mat2,
        formDisc (fixForm M).1 (fixForm M).2.1 (fixForm M).2.2 = traceDisc M) :=
  ⟨⟨fixForm_G, by decide, by decide⟩,
   ⟨fixForm_T, by decide, by decide⟩,
   ⟨fixForm_U, by decide, by decide⟩,
   fixForm_disc_eq_traceDisc⟩

/-! ## §5b — each fixed-point form is a named number-field norm -/

/-- `formEval (fixForm G) m k = goldenForm m k` — the fixed-point form of the hyperbolic
    boost is **exactly** the golden form `m² − mk − k²`, the disc-`+5` real-quadratic norm
    of `ℤ[φ]` (up to sign the field norm `N(m+kφ)`). -/
theorem formEval_G_eq_golden (m k : Int) :
    formEval (fixForm G) m k = goldenForm m k := by
  rw [fixForm_G]
  show (1 : Int) * (m * m) + (-1) * (m * k) + (-1) * (k * k) = m * m - m * k - k * k
  ring_intZ

/-- `formEval (fixForm U) a (−b) = eisForm a b` — the cyclotomic form `x² + xy + y²` is the
    `b ↦ −b` orientation of the Eisenstein norm `a² − ab + b²`.  Same disc-`−3` field
    `ℚ(ω)`, the two representatives differing only by the lattice orientation (`ω` vs `−ω`):
    the prose "equivalent representative" is this equation. -/
theorem formEval_U_eq_eis (a b : Int) :
    formEval (fixForm U) a (-b) = eisForm a b := by
  rw [fixForm_U]
  show (1 : Int) * (a * a) + 1 * (a * -b) + 1 * (-b * -b) = a * a - a * b + b * b
  ring_intZ

/-- `formEval (fixForm S) a b = a² + b²` — the fixed-point form of the order-4 generator is
    the **Gaussian norm** `‖a + bi‖²`, disc `−4`, the `j = 1728` CM point. -/
theorem formEval_S_eq_gaussian (a b : Int) :
    formEval (fixForm S) a b = a * a + b * b := by
  rw [fixForm_S]
  show (1 : Int) * (a * a) + 0 * (a * b) + 1 * (b * b) = a * a + b * b
  rw [E213.Meta.Int213.PolyIntM.one_mulZ, E213.Meta.Int213.PolyIntM.one_mulZ,
      E213.Meta.Int213.zero_mul, E213.Meta.Int213.add_comm (a * a) 0,
      E213.Meta.Int213.zero_add]

/-- ★★★ **The golden and Eisenstein reference forms are exactly preserved by their
    monodromy.**  Since `G, U ∈ SL(2,ℤ)` (`det = 1`), `fixForm_automorph` gives exact
    invariance: the golden form `m²−mk−k²` is conserved by the hyperbolic boost `G`, and
    the cyclotomic Eisenstein form `x²+x+1` by the elliptic rotation `U` — each reference
    form is the conserved quantity of the geodesic it labels. -/
theorem reference_forms_preserved (x y : Int) :
    formEval (fixForm G) (G.a * x + G.b * y) (G.c * x + G.d * y)
        = formEval (fixForm G) x y
    ∧ formEval (fixForm U) (U.a * x + U.b * y) (U.c * x + U.d * y)
        = formEval (fixForm U) x y := by
  refine ⟨?_, ?_⟩
  · rw [fixForm_automorph G x y, show G.a * G.d - G.b * G.c = 1 from by decide, Int.one_mul]
  · rw [fixForm_automorph U x y, show U.a * U.d - U.b * U.c = 1 from by decide, Int.one_mul]

/-- ★★★ **The elliptic conjecture, made exact: the sign of `D = tr²−4` is the line/cusp/curve
    dial.**  `traceDisc G > 0` (two real fixed points ⟹ a hyperbolic geodesic ⟹ the
    real-quadratic golden **line**); `traceDisc T = 0` (one repeated real fixed point at `∞`
    ⟹ parabolic ⟹ the rational **cusp**); `traceDisc U < 0` (a complex-conjugate
    fixed-point pair ⟹ an elliptic point of `ℍ` ⟹ the imaginary-quadratic Eisenstein
    **curve** / torus).  Mingu's "Eisenstein appears as a curve, not a line" is the `D < 0`
    face — definite norm ⟺ negative discriminant ⟺ complex fixed points ⟺ elliptic point ⟺
    bounded torus. -/
theorem disc_sign_is_line_cusp_curve :
    traceDisc G > 0 ∧ traceDisc T = 0 ∧ traceDisc U < 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetTraceField
