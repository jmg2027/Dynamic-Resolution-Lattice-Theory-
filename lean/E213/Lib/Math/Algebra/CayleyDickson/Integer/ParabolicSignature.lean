import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature

/-!
# ParabolicSignature — the degenerate (disc 0) reference completes the signature trichotomy

`EisensteinSignature` split the cross-determinant's reference forms by sign of
discriminant into the *indefinite* golden form (disc `+5`, a convergent **line**) and the
*positive-definite* Eisenstein norm (disc `−3`, a bounded **curve** / torus).  Between
them sits the **degenerate** case, discriminant `0` — the parabolic reference.  This file
adds it, completing the trichotomy that mirrors the `SL₂(ℤ)` trace trichotomy
(|trace| > 2 hyperbolic / = 2 parabolic / < 2 elliptic).

The disc-`0` form is a perfect square of a linear form; the cleanest representative is
`parabForm m k = (m − k)²`:

  * `parab_nonneg` — `0 ≤ (m−k)²` for all `m, k : Int` (a square; `sq_nonneg`).  Like the
    Eisenstein norm it is never negative — but, unlike it, **not** definite:
  * `parab_nonorigin_zero` — `parabForm 1 1 = 0`: the form vanishes *away from the
    origin* (in fact on the whole diagonal line `m = k`).  Definite (Eisenstein) vanishes
    only at the origin; the parabolic form is **semi-definite**, vanishing on a line.

So the three references are distinguished by where the form sits relative to `0`:

  * **disc `+5`** golden — takes a **negative** value (`signature_dichotomy`): indefinite,
    unbounded, a convergent **line** (the det-one floor, real-quadratic `ℤ[φ]`);
  * **disc `0`** parabolic — `≥ 0` with a **non-origin zero** (zero on a line): the
    degenerate **cusp** direction (the rationals — terminating cuts, the parabolic fixed
    point);
  * **disc `−3`** Eisenstein — `≥ 0`, definite: bounded, a **curve** / torus
    (imaginary-quadratic `ℤ[ω]`).

`signature_trichotomy` bundles all three.  The parabolic cusp is the boundary between the
completing line and the bounded curve — the rational direction, which in the divergence
picture is the genuine, irreducible divergence (the residue read in the geodesic
coding: the one cusp of `ℍ/SL₂(ℤ)`).

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ParabolicSignature

open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature
  (sq_nonneg eisForm eisForm_nonneg goldenForm)

/-- The degenerate (disc `0`) reference form: the perfect square `(m − k)²`. -/
def parabForm (m k : Int) : Int := (m - k) * (m - k)

/-- ★ **The parabolic form is nonnegative** — it is a square (`sq_nonneg`).  Like the
    Eisenstein norm it never goes negative; the difference is that it is not *definite*. -/
theorem parab_nonneg (m k : Int) : 0 ≤ parabForm m k := sq_nonneg (m - k)

/-- ★★ **The parabolic form has a non-origin zero**: `parabForm 1 1 = 0`.  It vanishes off
    the origin (on the whole diagonal `m = k`), so it is **semi-definite**, not definite —
    the degenerate / parabolic signature, distinguishing disc `0` from the definite
    Eisenstein (disc `−3`, zero only at the origin). -/
theorem parab_nonorigin_zero : parabForm 1 1 = 0 := by decide

/-- ★★★ **The signature trichotomy.**  The three cross-determinant reference forms, by
    sign of discriminant:

    1. **disc `+5` golden** — `∃ a b, goldenForm a b < 0`: *indefinite* (unbounded ⟹ a
       convergent line, the det-one floor);
    2. **disc `0` parabolic** — `∀ m k, 0 ≤ parabForm m k` with `parabForm 1 1 = 0`:
       *semi-definite*, vanishing on a line (the degenerate cusp / rational direction);
    3. **disc `−3` Eisenstein** — `∀ a b, 0 ≤ eisForm a b`: *positive-definite* (bounded
       ⟹ a curve / torus).

    Indefinite (line) ⟹ parabolic (cusp, boundary) ⟹ definite (curve): the sign of the
    discriminant is the shape of the reference, and the parabolic cusp is the boundary —
    the rational direction, the genuine divergence of the geodesic picture. -/
theorem signature_trichotomy :
    (∃ a b : Int, goldenForm a b < 0)
    ∧ ((∀ m k : Int, 0 ≤ parabForm m k) ∧ parabForm 1 1 = 0)
    ∧ (∀ a b : Int, 0 ≤ eisForm a b) :=
  ⟨⟨1, 1, by decide⟩, ⟨parab_nonneg, parab_nonorigin_zero⟩, eisForm_nonneg⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ParabolicSignature
