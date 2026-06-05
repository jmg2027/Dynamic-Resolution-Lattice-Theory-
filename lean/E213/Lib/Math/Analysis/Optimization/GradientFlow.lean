import E213.Meta.Int213.Core
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# Gradient-flow monotonicity, compiled to the proof-ISA (∅-axiom)

The structural reason Perelman's `𝓕/𝓦` is a monovariant under Ricci flow, with
the *standard proof* translated to `0`-axiom.

## Standard math (the reference proof)

For a functional `F` on an inner-product space, gradient flow is
`ẋ = −∇F(x)`, and the chain rule gives
`d/dt F(x(t)) = ⟨∇F, ẋ⟩ = −⟨∇F, ∇F⟩ = −‖∇F‖² ≤ 0`.
So `F` descends, at rate exactly the squared gradient norm — the monovariant is
*forced by the gradient structure*, not guessed.  For Ricci flow `F = 𝓕`,
`∇𝓕 = −(Ric + Hess f)` (the PDE computation), giving
`d𝓕/dt = 2∫|Ric + Hess f|²e^{−f} ≥ 0`.

## What the ISA compilation yields

Discretizing (the exact Euler / one gradient-descent step on the quadratic
`F(x) = ⟪x,x⟫`, `∇F = 2x`, step `x ↦ x − τ∇F`), the entire content is the
**descent identity**

  `F(x − τ∇F) = F(x) − τ(1−τ)·‖∇F(x)‖²`,

proven here from *only* symmetry + scalar-homogeneity of the inner product
(`ip_comm`, `ip_smul_left`) plus `ℤ`-ring normalization (`ring_intZ`, ∅-axiom).
This is the A6 FLOW **`descent` hypothesis discharged**: `F`'s per-step change is
gradient-norm-controlled and `≤ 0` (monotonicity, `gradient_descent_monotone`,
under `0 ≤ τ ≤ 1` + inner-product positivity).

## The instruction this compiles to is NOT A6

A6 FLOW (well-founded `ℕ`-monovariant) gives **finite-time** termination — that
fits the round sphere, where the flow is *linear* in `ρ = r²` and `ρ` hits `0`
(`RicciSphereFlow`).  Gradient flow is different: on `F(x)=⟪x,x⟫` with a
contractive `τ ∈ (0,1)` the value `F` decreases *geometrically*
(`F(x') = (1−2τ)²F(x)`), so it converges **asymptotically**, the infimum
attained only in the limit.  Compiled to the ISA this is the
**monotone + bounded-below ⟹ convergent** instruction (real-analysis
completeness, `Analysis/.../MonotonicBounded` + `CauchyComplete`), *not* the
well-founded `ℕ`-descent of A6.  So:

  · round-sphere Ricci flow  →  A6 FLOW (linear, finite extinction)
  · gradient-flow `𝓕`/`𝓦`   →  descent-identity + completeness-LOOP (asymptotic)

The descent identity below is the part of Perelman's monotonicity that is
*structural* (forced by the gradient + inner product); the geometric core
(`∇𝓕 = −(Ric+Hess f)`, surgery) remains the open frontier
(`research-notes/frontiers/ricci_flow_smooth_core.md`).  Working over `ℤ`
scalars keeps the descent identity a pure ring fact; strict (geometric) descent
needs a contractive rational `τ`, the asymptotic case above.
-/

namespace E213.Lib.Math.Analysis.Optimization.GradientFlow

open E213.Meta.Int213

/-- A minimal inner-product space over `ℤ` scalars: the algebraic skeleton on
    which the gradient-descent descent identity lives.  Fields are exactly the
    inner-product / vector-space laws the standard proof uses. -/
structure IPSpace where
  /-- the vector carrier -/
  V : Type
  /-- vector addition -/
  add : V → V → V
  /-- scalar multiplication by an integer -/
  smul : Int → V → V
  /-- the (ℤ-valued) inner product -/
  ip : V → V → Int
  /-- symmetry `⟪u,v⟫ = ⟪v,u⟫` -/
  ip_comm : ∀ u v, ip u v = ip v u
  /-- scalar-homogeneity in the left argument `⟪a•u,v⟫ = a·⟪u,v⟫` -/
  ip_smul_left : ∀ (a : Int) (u v), ip (smul a u) v = a * ip u v
  /-- `a•(b•v) = (a·b)•v` -/
  smul_smul : ∀ (a b : Int) (v), smul a (smul b v) = smul (a * b) v
  /-- `1•v = v` -/
  smul_one : ∀ v, smul 1 v = v
  /-- `a•v + b•v = (a+b)•v` -/
  add_smul_same : ∀ (a b : Int) (v), add (smul a v) (smul b v) = smul (a + b) v
  /-- positivity `0 ≤ ⟪v,v⟫` (the form is positive semidefinite) -/
  ip_nonneg : ∀ v, (0 : Int) ≤ ip v v

variable (S : IPSpace)

/-- The quadratic functional `F(x) = ⟪x,x⟫`. -/
def F (x : S.V) : Int := S.ip x x

/-- The gradient of `F` at `x`: `∇(⟪x,x⟫) = 2x`. -/
def gradF (x : S.V) : S.V := S.smul 2 x

/-- One gradient-descent step `x ↦ x − τ·∇F(x)`. -/
def gradStep (τ : Int) (x : S.V) : S.V := S.add x (S.smul (-τ) (gradF S x))

/-- `x + c•x = (1+c)•x`. -/
theorem combine (c : Int) (x : S.V) : S.add x (S.smul c x) = S.smul (1 + c) x := by
  calc S.add x (S.smul c x)
      = S.add (S.smul 1 x) (S.smul c x) := by rw [S.smul_one]
    _ = S.smul (1 + c) x := S.add_smul_same 1 c x

/-- The gradient-descent step in closed form: `x − τ·(2x) = (1−2τ)x`. -/
theorem gradStep_eq (τ : Int) (x : S.V) :
    gradStep S τ x = S.smul (1 + (-τ) * 2) x := by
  unfold gradStep gradF
  rw [S.smul_smul, combine S]

/-- `F(s•x) = s²·F(x)` — from symmetry + scalar-homogeneity of the inner
    product. -/
theorem F_smul (s : Int) (x : S.V) : F S (S.smul s x) = (s * s) * F S x := by
  show S.ip (S.smul s x) (S.smul s x) = (s * s) * S.ip x x
  rw [S.ip_smul_left, S.ip_comm x (S.smul s x), S.ip_smul_left]
  ring_intZ

/-- `‖∇F(x)‖² = ⟪2x,2x⟫ = 4·F(x)`. -/
theorem normSq_gradF (x : S.V) : S.ip (gradF S x) (gradF S x) = 4 * F S x := by
  show F S (S.smul 2 x) = 4 * F S x
  rw [F_smul]
  ring_intZ

/-- ★★★★★ **The gradient-descent descent identity** (the ISA payload).

    `F(x − τ∇F) = F(x) − τ(1−τ)·‖∇F(x)‖²` — the per-step change of the
    monovariant `F` is exactly the (scaled) squared gradient norm, *forced* by
    the inner-product structure.  The discrete `0`-axiom translation of
    `d/dt F = −‖∇F‖²`, the structural heart of Perelman's `𝓕/𝓦` monotonicity. -/
theorem gradient_descent_identity (τ : Int) (x : S.V) :
    F S (gradStep S τ x)
      = F S x - τ * (1 - τ) * S.ip (gradF S x) (gradF S x) := by
  rw [gradStep_eq, F_smul, normSq_gradF]
  ring_intZ

/-- ★★★★★ **Monotonicity**: for a contractive-range step `0 ≤ τ ≤ 1`, `F` does
    not increase — the descent deficit `τ(1−τ)‖∇F‖²` is `≥ 0` (product of
    nonnegatives + inner-product positivity).  This is the A6 `descent`
    hypothesis, here *derived* from the gradient structure rather than assumed. -/
theorem gradient_descent_monotone (τ : Int) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (x : S.V) : F S (gradStep S τ x) ≤ F S x := by
  rw [gradient_descent_identity]
  have h1τ : (0 : Int) ≤ 1 - τ := Order.le_zero_of_nonneg (Order.sub_nonneg_of_le hτ1)
  have hD : (0 : Int) ≤ τ * (1 - τ) * S.ip (gradF S x) (gradF S x) :=
    mul_nonneg (mul_nonneg hτ0 h1τ) (S.ip_nonneg _)
  apply Order.le_of_sub_nonneg
  apply Order.nonneg_of_le_zero
  have hid : F S x - (F S x - τ * (1 - τ) * S.ip (gradF S x) (gradF S x))
              = τ * (1 - τ) * S.ip (gradF S x) (gradF S x) := by ring_intZ
  rw [hid]; exact hD

end E213.Lib.Math.Analysis.Optimization.GradientFlow
