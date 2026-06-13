import E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistConic

/-!
# FloorReferenceForm — the det-one floor's reference form is indefinite (the disc+5 line)

The completability stratification's trivially-free bottom is the **det-one floor**
(`W ≡ 1`, `DepthFloorDetOne`; `RateStratification.floor_carries_Htel`).  Its conserved
invariant is the golden form `Q(m,k) = m² − mk − k²` — the `P = [[2,1],[1,1]]` orbit's
shape-label (`ProbeTwistConic.Q_preserved`).  This file records the completability-side
fact that complements the algebra-side `CayleyDickson/Integer/EisensteinSignature`: that
golden form is **indefinite**.

Indefinite means the floor's orbits populate **both** branches of the hyperbola
`Q = N` (discriminant `+5 = NS + NT > 0`):

  * `golden_indefinite` — `Q` takes both signs over `ℕ`: the `(2,1)`-orbit sits on
    `Q = +1` (`m·k + k² < m²` at `(2,1)`), the φ-convergents on `Q = −1`
    (`m² < m·k + k²` at `(1,1)`).
  * `floor_reference_is_indefinite` — bundles it with `Q_preserved`: the det-one floor
    *preserves* the golden form, and that form is indefinite.  Indefinite ⟹ unbounded
    (hyperbolic) level sets ⟹ an infinite convergent **line** (the `ℤ[φ]` unit group
    `φⁿ` = the P-orbit), which is exactly why the floor completes with a closed-form
    modulus — the real-quadratic, disc `+5` rung of the completability tower.

This is the bottom rung of the completability stratification made into a theorem,
in-track: the rung floor's algebraic character is the **indefinite** (disc `> 0`) golden
reference, the line side of the discriminant-sign dichotomy whose definite (disc `< 0`,
Eisenstein, curve) side lives in `EisensteinSignature`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm
open E213.Lib.Math.NumberSystems.Real213.ProbeTwist

open E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistConic (Q_preserved)

/-- ★★ **The golden form `m² − mk − k²` is indefinite over `ℕ`.**  It takes both signs:
    `Q(2,1) = +1` (the `(2,1)`-orbit branch, `mk+k² < m²`) and `Q(1,1) = −1` (the
    φ-convergent branch, `m² < mk+k²`).  So the det-one floor's reference form has orbits
    on both branches of its hyperbola — the indefinite, disc `+5` signature. -/
theorem golden_indefinite :
    (∃ m k : Nat, m * k + k * k < m * m) ∧ (∃ m k : Nat, m * m < m * k + k * k) :=
  ⟨⟨2, 1, by decide⟩, ⟨1, 1, by decide⟩⟩

/-- ★★★ **The det-one floor's reference form is indefinite.**  The floor's `P`-step
    `(m,k) ↦ (2m+k, m+k)` *preserves* the golden form (`Q_preserved` — the conserved
    `Q = N` level set), and that form is indefinite (`golden_indefinite` — both branches
    occur).  Preserved indefinite form ⟹ unbounded hyperbolic orbits ⟹ a convergent
    line: the det-one floor is the real-quadratic (disc `+5`) rung, the completing bottom
    of the stratification.  (The definite, disc `−3` Eisenstein side — bounded, a curve —
    is `CayleyDickson/Integer/EisensteinSignature.signature_dichotomy`.) -/
theorem floor_reference_is_indefinite :
    (∀ m k : Nat,
        (2*m+k)*(2*m+k) + m*k + k*k = (2*m+k)*(m+k) + (m+k)*(m+k) + m*m)
    ∧ ((∃ m k : Nat, m * k + k * k < m * m) ∧ (∃ m k : Nat, m * m < m * k + k * k)) :=
  ⟨Q_preserved, golden_indefinite⟩

end E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm
