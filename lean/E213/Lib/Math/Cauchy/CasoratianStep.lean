import E213.Meta.Tactic.NatHelper

/-!
# CasoratianStep — the discrete-Wronskian (Abel/Liouville) law for a 3-term recurrence

A second-order holonomic (P-recursive) recurrence `c₂(n)·xₙ = c₁(n)·xₙ₋₁ + c₀(n)·xₙ₋₂`
has, for any two solutions `a`, `b`, a **Casoratian** (discrete Wronskian)
`Cₙ = aₙ·bₙ₋₁ − aₙ₋₁·bₙ`.  The classical fact (the discrete analog of Abel's identity)
is that the middle coefficient `c₁` cancels and the Casoratian propagates by the *outer*
coefficients alone:

    c₂(n)·Cₙ = −c₀(n)·Cₙ₋₁.

This file proves that law in a **subtraction-free `ℕ` form** — moving the minus across so
no `Nat` truncation occurs — for arbitrary `ℕ`-valued coefficient values and sequence
values satisfying the two recurrence equations:

    c₂·a₂·b₁ + c₀·a₁·b₀ = c₂·a₁·b₂ + c₀·a₀·b₁,

where `(a₀,a₁,a₂) = (aₙ₋₂,aₙ₋₁,aₙ)` and `(c₂,c₁,c₀) = (c₂(n),c₁(n),c₀(n))`.  Both sides
expand (using the two recurrence hypotheses) to the common value
`c₁·a₁·b₁ + c₀·a₀·b₁ + c₀·a₁·b₀`, so the identity holds with no sign or integer
machinery — pure `ℕ`, ∅-axiom.

**Consequence for the Apéry zeta tower** (`DepthAperyCubic`).  The propagation depends
only on the outer coefficients `c₂`, `c₀`:

  * ζ(2): `c₂ = (n+1)²`, `c₀ = n²` (degree 2) ⟹ `(n+1)²·Cₙ = −n²·Cₙ₋₁` ⟹ `Cₙ ∝ ±1/n²`;
  * ζ(3): `c₂ = n³` (`aperyTop`), `c₀ = (n−1)³` (`aperyBot`) (degree 3)
    ⟹ `n³·Cₙ = (n−1)³·Cₙ₋₁` ⟹ `Cₙ ∝ 1/n³`.

So the Casoratian denominator degree (`2`, `3`) is exactly the degree of the outer
coefficients — the polynomials `zeta2Top`/`zeta2Bot`, `aperyTop`/`aperyBot` of
`DepthAperyCubic`, of finite-difference depth `2`, `3`.  This is why the
**coefficient-degree tower is the invariant the discrete Wronskian sees**, and why the
middle coefficient (`11n²+11n+3`, `34n³−51n²+27n−5`), though the same degree, does not
enter.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.CasoratianStep

open E213.Tactic.NatHelper (add_mul mul_assoc mul_left_comm)

/-- ★★★ **The Casoratian step law, subtraction-free over `ℕ`.**  For any coefficient
    values `c₂,c₁,c₀` and any two sequence triples `(a₀,a₁,a₂)`, `(b₀,b₁,b₂)` satisfying
    the same 3-term recurrence `c₂·x₂ = c₁·x₁ + c₀·x₀`, the cross terms obey

        c₂·(a₂·b₁) + c₀·(a₁·b₀) = c₂·(a₁·b₂) + c₀·(a₀·b₁).

    This is `c₂·Cₙ = −c₀·Cₙ₋₁` (`C = a·b₋₁ − a₋₁·b`) with the minus moved across — the
    discrete analog of Abel's identity, the middle coefficient `c₁` cancelling.  Both
    sides reduce to `c₁·(a₁·b₁) + c₀·(a₀·b₁) + c₀·(a₁·b₀)`; ∅-axiom, no integers. -/
theorem casoratian_step
    (c₂ c₁ c₀ a₀ a₁ a₂ b₀ b₁ b₂ : Nat)
    (ha : c₂ * a₂ = c₁ * a₁ + c₀ * a₀)
    (hb : c₂ * b₂ = c₁ * b₁ + c₀ * b₀) :
    c₂ * (a₂ * b₁) + c₀ * (a₁ * b₀) = c₂ * (a₁ * b₂) + c₀ * (a₀ * b₁) := by
  -- left cross term, via the `a`-recurrence
  have lhs : c₂ * (a₂ * b₁) = c₁ * (a₁ * b₁) + c₀ * (a₀ * b₁) := by
    rw [← mul_assoc c₂ a₂ b₁, ha, add_mul, mul_assoc c₁ a₁ b₁, mul_assoc c₀ a₀ b₁]
  -- right cross term, via the `b`-recurrence
  have rhs : c₂ * (a₁ * b₂) = c₁ * (a₁ * b₁) + c₀ * (a₁ * b₀) := by
    rw [mul_left_comm c₂ a₁ b₂, hb, Nat.mul_add, mul_left_comm a₁ c₁ b₁, mul_left_comm a₁ c₀ b₀]
  rw [lhs, rhs,
      Nat.add_assoc (c₁ * (a₁ * b₁)) (c₀ * (a₀ * b₁)) (c₀ * (a₁ * b₀)),
      Nat.add_assoc (c₁ * (a₁ * b₁)) (c₀ * (a₁ * b₀)) (c₀ * (a₀ * b₁)),
      Nat.add_comm (c₀ * (a₀ * b₁)) (c₀ * (a₁ * b₀))]

/-- A self-Casoratian collapse: applied to a *single* solution (`a = b`), both cross
    terms coincide (`a₂·a₁ = a₁·a₂`), so the law degenerates to the trivial
    `c₂·(a₂·a₁) + c₀·(a₁·a₀) = c₂·(a₁·a₂) + c₀·(a₀·a₁)` — the Casoratian of a solution
    with itself is `0`, as it must be.  (A sanity instance, no new content.) -/
theorem casoratian_self
    (c₂ c₁ c₀ a₀ a₁ a₂ : Nat)
    (ha : c₂ * a₂ = c₁ * a₁ + c₀ * a₀) :
    c₂ * (a₂ * a₁) + c₀ * (a₁ * a₀) = c₂ * (a₁ * a₂) + c₀ * (a₀ * a₁) :=
  casoratian_step c₂ c₁ c₀ a₀ a₁ a₂ a₀ a₁ a₂ ha ha

end E213.Lib.Math.Cauchy.CasoratianStep
