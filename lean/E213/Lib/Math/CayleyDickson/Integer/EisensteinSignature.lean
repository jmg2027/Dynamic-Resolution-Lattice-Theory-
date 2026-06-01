import E213.Lib.Math.CayleyDickson.Integer.ZOmega
import E213.Meta.Int213.PolyInt2
import E213.Meta.Int213.Core

/-!
# EisensteinSignature — the Eisenstein norm is positive-definite (definite ⇒ curve)

The cross-determinant classification's number-field reading turns "Eisenstein appears
as an elliptic *curve*, not a *line*" into a statement about the **sign of the
discriminant**: the golden form `m²−mk−k²` (disc `+5`) is *indefinite* (unbounded level
sets ⟹ a convergent line), while the Eisenstein norm `a²−ab+b²` (disc `−3`) is
*positive-definite* (bounded level sets ⟹ a torus = the `j=0` elliptic curve's period
lattice).  This file proves that dichotomy ∅-axiom, via the bivariate `Int` reflection
prover `Meta.Int213.PolyInt2`.

  * ★ `eisForm_nonneg` — `0 ≤ a²−ab+b²` for all `a b : Int`, through the identity
    `2·(a²−ab+b²) = a² + b² + (a−b)²` (`two_eisForm`, by `poly_id2`) and the
    sum-of-squares being nonneg.  `eisenstein_norm_nonneg`: the same for `ZOmega.normSq`.
  * ★ `golden_indefinite` — `goldenForm 1 0 = 1`, `goldenForm 1 1 = −1`: the golden form
    takes both signs.
  * ★★★ `signature_dichotomy` — the Eisenstein norm is **definite** (never negative)
    while the golden form is **indefinite** (takes a negative value).  Definite ⟹
    bounded level sets ⟹ a curve; indefinite ⟹ unbounded ⟹ a line.  The ∅-axiom heart
    of the conjecture that the Eisenstein reference appears as a curve, not a line.

All zero-axiom.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.EisensteinSignature

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Meta.Int213.PolyInt2 (PE2 poly_id2)
open E213.Meta.Int213 (add_nonneg nonneg_of_add_self add_eq_zero_of_nonneg mul_eq_zero)

/-! ## §1 — squares are nonnegative over `Int` (constructor cases, no `Int.le_total`) -/

/-- `0 ≤ a * a` for every `a : Int` — by cases on the constructor, avoiding the
    propext-dirty `Int.le_total`. -/
theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases a with
  | ofNat n   => exact Int.ofNat_nonneg (n * n)
  | negSucc n => rw [Int.negSucc_mul_negSucc]; exact Int.ofNat_nonneg _

/-! ## §2 — the Eisenstein norm form and its positive-definiteness -/

/-- The Eisenstein norm as a binary `Int` form: `a² − ab + b²` (= `ZOmega.normSq`). -/
def eisForm (a b : Int) : Int := a * a - a * b + b * b

/-- ★ **The `2·N` sum-of-squares identity.**  `(a²−ab+b²) + (a²−ab+b²) = a² + b² +
    (a−b)²` — proved by the bivariate `Int` reflection prover.  The RHS is manifestly a
    sum of squares. -/
theorem two_eisForm (a b : Int) :
    eisForm a b + eisForm a b = a * a + b * b + (a - b) * (a - b) :=
  poly_id2
    (.add (.add (.add (.mul .X .X) (.neg (.mul .X .Y))) (.mul .Y .Y))
          (.add (.add (.mul .X .X) (.neg (.mul .X .Y))) (.mul .Y .Y)))
    (.add (.add (.mul .X .X) (.mul .Y .Y))
          (.mul (.add .X (.neg .Y)) (.add .X (.neg .Y))))
    rfl a b

/-- ★ **The Eisenstein form is nonnegative.**  `0 ≤ a²−ab+b²` for all `a b : Int`:
    `2·N` is a sum of three squares (`two_eisForm` + `sq_nonneg`), and
    `nonneg_of_add_self` descends from `0 ≤ N+N`. -/
theorem eisForm_nonneg (a b : Int) : 0 ≤ eisForm a b := by
  have hsum : 0 ≤ a * a + b * b + (a - b) * (a - b) :=
    add_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg (a - b))
  rw [← two_eisForm a b] at hsum
  exact nonneg_of_add_self hsum

/-- `eisForm` is exactly `ZOmega.normSq` (definitional). -/
theorem eisForm_eq_normSq (u : ZOmega) : eisForm u.re u.im = u.normSq := rfl

/-- ★ **The Eisenstein integer norm is nonnegative.**  `0 ≤ u.normSq` for every
    `u : ℤ[ω]` — a definite form. -/
theorem eisenstein_norm_nonneg (u : ZOmega) : 0 ≤ u.normSq := by
  rw [← eisForm_eq_normSq u]; exact eisForm_nonneg u.re u.im

/-- ★★ **The Eisenstein norm is anisotropic.**  `normSq u = 0 → u = 0`: the form
    vanishes only at the origin.  From `2·N = re² + im² + (re−im)²` a zero norm forces
    all three squares to vanish (`add_eq_zero_of_nonneg`), hence `re = im = 0`
    (`mul_eq_zero`).  Together with `eisenstein_norm_nonneg` this is full
    **positive-definiteness**. -/
theorem eisenstein_norm_zero (u : ZOmega) (h : u.normSq = 0) : u = 0 := by
  have he : eisForm u.re u.im = 0 := by rw [eisForm_eq_normSq u]; exact h
  have h2 : u.re * u.re + u.im * u.im + (u.re - u.im) * (u.re - u.im) = 0 := by
    have ht := two_eisForm u.re u.im
    rw [he, Int.add_zero] at ht
    exact ht.symm
  have hsplit := add_eq_zero_of_nonneg
    (add_nonneg (sq_nonneg u.re) (sq_nonneg u.im)) (sq_nonneg (u.re - u.im)) h2
  have hab := add_eq_zero_of_nonneg (sq_nonneg u.re) (sq_nonneg u.im) hsplit.1
  exact ZOmega.ext ((mul_eq_zero hab.1).elim id id) ((mul_eq_zero hab.2).elim id id)

/-- ★★★ **The Eisenstein norm is positive-definite** — nonnegative and vanishing only
    at the origin. -/
theorem eisenstein_norm_posdef (u : ZOmega) :
    0 ≤ u.normSq ∧ (u.normSq = 0 → u = 0) :=
  ⟨eisenstein_norm_nonneg u, eisenstein_norm_zero u⟩

/-! ## §3 — the golden form is indefinite, and the dichotomy -/

/-- The golden form `a² − ab − b²` (disc `+5`, the `√5`/φ form). -/
def goldenForm (a b : Int) : Int := a * a - a * b - b * b

/-- The golden form takes **both** signs: `goldenForm 1 0 = 1`, `goldenForm 1 1 = −1`. -/
theorem golden_indefinite : goldenForm 1 0 = 1 ∧ goldenForm 1 1 = -1 := by
  decide

/-- ★★★ **The signature dichotomy.**  The Eisenstein norm is **definite** — never
    negative (`∀ a b, 0 ≤ eisForm a b`); the golden form is **indefinite** — it takes a
    negative value (`goldenForm 1 1 = −1 < 0`).  Definite ⟹ bounded level sets ⟹ the
    Eisenstein reference is a torus / elliptic curve; indefinite ⟹ unbounded level sets
    ⟹ the golden reference is a convergent line.  The ∅-axiom core of the conjecture
    that the Eisenstein reference appears as a curve, not a line. -/
theorem signature_dichotomy :
    (∀ a b : Int, 0 ≤ eisForm a b) ∧ (∃ a b : Int, goldenForm a b < 0) :=
  ⟨eisForm_nonneg, ⟨1, 1, by decide⟩⟩

end E213.Lib.Math.CayleyDickson.Integer.EisensteinSignature
