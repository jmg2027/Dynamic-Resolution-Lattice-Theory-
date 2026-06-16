import E213.Lib.Math.Geometry.DiscreteCurvature.RicciSphereFlow

/-!
# Homogeneous Ricci flow: the Einstein trichotomy (∅-axiom)

Extends `RicciSphereFlow` (the round sphere) to the full **Einstein trichotomy**
of homogeneous Ricci flow.  On a homogeneous Einstein metric `Ric = λ·g` the flow
`∂_t g = −2 Ric` is the scalar ODE `dρ/dt = −2λ` on the size `ρ`; the *sign* of the
Einstein constant `λ` determines the entire qualitative behaviour:

  · **λ > 0** (positive Einstein — round sphere): `ρ` decreases linearly, **finite
    extinction** to a point.  Lifts to the FLOW archetype (well-founded `ℕ`-descent),
    `RicciSphereFlow.sphere_reaches_extinction`.
  · **λ = 0** (Ricci-flat — flat torus / Calabi–Yau): `dρ/dt = 0`, the metric is
    **stationary** — every state is already its normal form (`flat_torus_stationary`).
  · **λ < 0** (negative Einstein — hyperbolic): `ρ` grows without bound, the flow
    **diverges**, never reaching a fixed point (`hyperbolic_diverges`,
    `expand_no_fixed`) — there is no normal form to descend to.

The fixed points of the (unnormalized) homogeneous flow are exactly the
Ricci-flat metrics (`λ = 0`); the three regimes are the three signs of `λ` — the
discrete `0`-axiom shadow of "Einstein metrics are the Ricci solitons, and their
sign sets shrink/steady/expand."

## Honest scope

The homogeneous / ODE case (as in `RicciSphereFlow`): the rate `r ∝ |λ|` is the
geometric *input* (the Einstein constant), not derived; smooth-metric general
Ricci flow is not treated here.
What is proven is the exact qualitative trichotomy the sign of `λ` forces on the
size ODE — the other homogeneous flows and the Einstein fixed points.
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.RicciHomogeneous

open E213.Lib.Math.Foundations.MonovariantFlow (iter)
open E213.Lib.Math.Geometry.DiscreteCurvature.RicciSphereFlow (step sphere_reaches_extinction)

/-! ## λ = 0 — Ricci-flat (flat torus): stationary -/

/-- **Flat torus / Ricci-flat**: at Einstein constant `λ = 0` the size does not
    move — the flow is the identity, every metric is its own normal form. -/
theorem flat_torus_stationary (ρ : Nat) : step 0 ρ = ρ := by
  show ρ - 0 = ρ
  exact Nat.sub_zero ρ

/-! ## λ < 0 — negative Einstein (hyperbolic): expansion / divergence -/

/-- The expanding flow `ρ ↦ ρ + r` of a negative-Einstein homogeneous metric
    (`dρ/dt = −2λ > 0`). -/
def expandStep (r ρ : Nat) : Nat := ρ + r

/-- Closed form of the expanding flow: after `k` steps the size is `ρ + k·r`. -/
theorem expand_iter : ∀ (r k ρ : Nat), iter (expandStep r) k ρ = ρ + k * r
  | r, 0, ρ => by show ρ = ρ + 0 * r; rw [Nat.zero_mul, Nat.add_zero]
  | r, k + 1, ρ => by
      show iter (expandStep r) k (expandStep r ρ) = ρ + (k + 1) * r
      rw [expand_iter r k (expandStep r ρ)]
      show ρ + r + k * r = ρ + (k + 1) * r
      rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm r (k * r)]

/-- The expanding flow has **no fixed point** (for `r > 0`): `ρ + r ≠ ρ`. -/
theorem expand_no_fixed (r ρ : Nat) (hr : 0 < r) : expandStep r ρ ≠ ρ := by
  show ρ + r ≠ ρ
  have h : ρ + 0 < ρ + r := Nat.add_lt_add_left hr ρ
  rw [Nat.add_zero] at h
  intro heq
  rw [heq] at h
  exact Nat.lt_irrefl ρ h

/-- **Divergence**: the expanding flow exceeds every bound `B` — no normal form,
    so A6 does not apply. -/
theorem hyperbolic_diverges (r ρ : Nat) (hr : 0 < r) (B : Nat) :
    ∃ k, B < iter (expandStep r) k ρ := by
  refine ⟨B + 1, ?_⟩
  rw [expand_iter]
  calc B < B + 1 := Nat.lt_succ_self B
    _ ≤ (B + 1) * r := Nat.le_mul_of_pos_right (B + 1) hr
    _ ≤ ρ + (B + 1) * r := Nat.le_add_left _ _

/-! ## The trichotomy -/

/-- ★★★★★★ **The Einstein trichotomy of homogeneous Ricci flow.**  The sign of
    the Einstein constant `λ` (encoded in the rate `r`) determines the flow:
    `λ = 0` stationary, `λ > 0` finite extinction, `λ < 0` divergence
    (no fixed point). -/
theorem einstein_trichotomy (ρ : Nat) :
    -- λ = 0 (Ricci-flat / flat torus): stationary
    (step 0 ρ = ρ)
    -- λ > 0 (positive Einstein / sphere): finite extinction
    ∧ (∀ r, 0 < r → ∃ k, iter (step r) k ρ = 0)
    -- λ < 0 (negative Einstein / hyperbolic): diverges, no fixed point
    ∧ (∀ r, 0 < r → (∀ B, ∃ k, B < iter (expandStep r) k ρ)
                    ∧ expandStep r ρ ≠ ρ) :=
  ⟨flat_torus_stationary ρ,
   fun r hr => sphere_reaches_extinction r hr ρ,
   fun r hr => ⟨hyperbolic_diverges r ρ hr, expand_no_fixed r ρ hr⟩⟩

end E213.Lib.Math.Geometry.DiscreteCurvature.RicciHomogeneous
