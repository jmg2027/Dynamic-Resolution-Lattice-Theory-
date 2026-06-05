import E213.Lib.Math.Foundations.MonovariantFlow

/-!
# Round-sphere Ricci flow → finite extinction, via A6 FLOW (∅-axiom)

The genuinely *smooth-metric* simplest case of Ricci flow, done honestly.

On a homogeneous space the Ricci-flow PDE `∂_t g = −2 Ric(g)` collapses to an
**ODE** on the finite-dimensional space of invariant metrics.  For the round
`n`-sphere `g = r²·g₀` (`g₀` = unit round metric) the curvature is the genuine
geometric input:

  `Ric(g₀) = (n−1)·g₀`,  and `Ric` is scale-invariant: `Ric(r²·g₀) = (n−1)·g₀`.

So Ricci flow reads `∂_t(r²·g₀) = −2(n−1)·g₀`, i.e. the **squared radius**
`ρ = r²` obeys the linear ODE `dρ/dt = −2(n−1)`.  Hence `ρ(t) = ρ₀ − 2(n−1)t`
strictly decreases and hits `0` at `t* = ρ₀ / (2(n−1))`: the sphere shrinks to a
round point in **finite time** — the `n = 3` seed of Perelman's finite-extinction
theorem.

Because the flow is *linear* in `ρ`, the explicit Euler step `ρ ↦ ρ − 2(n−1)` is
**exact** (no discretization error) at integer times, so the discrete flow below
*is* the round-sphere Ricci flow on `ρ`, not an approximation.  It compiles
directly onto the A6 FLOW archetype (`MonovariantFlow.flow_reaches`): monovariant
`ρ`, descent rate the genuine Ricci curvature `2(n−1)`, normal form `ρ = 0` =
extinction (the point).

## Honest scope — what this is NOT

This is the *homogeneous / ODE* case (the standard first Ricci-flow exercise),
**not** the core of the conjecture.  The hard content — `𝓕/𝓦`-entropy
monotonicity for *arbitrary* metrics (the proof that the descent hypothesis
holds, which here is trivial), non-collapsing, neck-pinch singularity analysis,
and surgery — requires Riemannian geometry + PDE theory absent from this repo
(Mathlib-forbidden) and is genuinely Fields-level.  The curvature value
`Ric(round Sⁿ) = (n−1)g` is an **input** here (encoded in `ricciRate`), not
derived.  The open core is recorded at
`research-notes/frontiers/ricci_flow_smooth_core.md`.
-/

namespace E213.Lib.Math.Geometry.GeometrizationConjecture.RicciSphereFlow

open E213.Lib.Math.Foundations.MonovariantFlow (iter IsNormalForm flow_reaches)

/-- The normalized Ricci-flow rate of the round `n`-sphere on the squared
    radius: `dρ/dt = −2(n−1)`.  Geometric input (`Ric(round Sⁿ) = (n−1)g` +
    scale-invariance of `Ric`), not derived here. -/
def ricciRate (n : Nat) : Nat := 2 * (n - 1)

/-- One exact Euler step of the round-sphere Ricci flow on `ρ = r²`:
    subtract the curvature rate `r`.  Extinction `ρ = 0` (the round point) is
    the absorbing normal form. -/
def step (r ρ : Nat) : Nat := ρ - r

/-- The squared radius strictly shrinks off extinction (rate `r > 0`): the A6
    descent hypothesis, here a one-line consequence of positivity of the
    curvature — *this triviality is exactly what is hard for general metrics*. -/
theorem step_descent (r : Nat) (hr : 0 < r) :
    ∀ ρ, step r ρ < ρ ∨ step r ρ = ρ := by
  intro ρ
  cases Nat.eq_zero_or_pos ρ with
  | inl h => right; rw [h]; exact Nat.zero_sub r
  | inr h => left; exact Nat.sub_lt h hr

/-- ★★★★★ **A6 FLOW fires: the round-sphere flow converges to a normal form**
    for any positive curvature rate and any initial radius. -/
theorem sphere_flow_converges (r : Nat) (hr : 0 < r) (ρ₀ : Nat) :
    ∃ k, IsNormalForm (step r) (iter (step r) k ρ₀) :=
  flow_reaches (step r) (fun ρ => ρ) (step_descent r hr) ρ₀

/-- The only normal form of the flow (for `r > 0`) is extinction `ρ = 0`. -/
theorem fixed_imp_zero (r : Nat) (hr : 0 < r) :
    ∀ ρ, step r ρ = ρ → ρ = 0 := by
  intro ρ h
  cases Nat.eq_zero_or_pos ρ with
  | inl hz => exact hz
  | inr hp =>
      have hlt : step r ρ < ρ := Nat.sub_lt hp hr
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl ρ)

/-- ★★★★★ **Finite extinction.**  The round-sphere Ricci flow reaches
    `ρ = 0` (the sphere shrinks to a round point) in finitely many steps —
    driven by the A6 FLOW archetype, normal form identified as extinction. -/
theorem sphere_reaches_extinction (r : Nat) (hr : 0 < r) (ρ₀ : Nat) :
    ∃ k, iter (step r) k ρ₀ = 0 := by
  obtain ⟨k, hk⟩ := sphere_flow_converges r hr ρ₀
  exact ⟨k, fixed_imp_zero r hr _ hk⟩

/-- `Ric`-rate of the round `n`-sphere is positive for `n ≥ 2`. -/
theorem ricciRate_pos : ∀ n, 2 ≤ n → 0 < ricciRate n
  | 0,    h => absurd h (by decide)
  | 1,    h => absurd h (by decide)
  | k+2, _ => by
      show 0 < 2 * (k + 1)
      rw [Nat.mul_succ]
      exact Nat.zero_lt_succ _

/-- ★★★★★★ **Round Sⁿ Ricci flow extinguishes in finite time (n ≥ 2).**
    The squared radius reaches `0`: the round sphere shrinks to a point. -/
theorem round_sphere_extinction (n : Nat) (hn : 2 ≤ n) (ρ₀ : Nat) :
    ∃ k, iter (step (ricciRate n)) k ρ₀ = 0 :=
  sphere_reaches_extinction (ricciRate n) (ricciRate_pos n hn) ρ₀

/-- ★★★★★★ **Round S³ Ricci flow finite extinction (the Poincaré case).**
    `Ric(round S³) = 2g`, so `dρ/dt = −4`; the 3-sphere shrinks to a round
    point in finite time — the `n = 3` seed of Perelman's finite-extinction
    theorem.  Driven by A6 FLOW. -/
theorem round_S3_ricci_extinction (ρ₀ : Nat) :
    ricciRate 3 = 4 ∧ ∃ k, iter (step (ricciRate 3)) k ρ₀ = 0 :=
  ⟨by decide, sphere_reaches_extinction (ricciRate 3) (by decide) ρ₀⟩

end E213.Lib.Math.Geometry.GeometrizationConjecture.RicciSphereFlow
