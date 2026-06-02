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

**Scope.**  This is the subtraction-free *identity* only — the discrete Abel/summation-by-
parts kernel.  The signed closed forms `Cₙ = ±5/n²` (ζ(2)), `±6/n³` (ζ(3)) require an
`ℤ`/`ℚ` ambient and the sign-alternation of `Cₙ` (and the telescoping product); they are a
separate, harder statement and are **not** proved here.  What this ℕ identity *does* give,
cleanly and ∅-axiom, is the structural content that **the middle coefficient `c₁` cancels**,
so the Casoratian propagates by the **outer** coefficients `c₂`, `c₀` alone.

**Connection to the Apéry zeta tower** (`DepthAperyCubic`).  Because only `c₂`, `c₀`
propagate the Casoratian, the relevant degree is `deg c₂ = deg c₀`: `(n+1)²`/`n²` (degree
2) for ζ(2), `n³` (`aperyTop`)/`(n−1)³` (`aperyBot`) (degree 3) for ζ(3) — the polynomials
of `DepthAperyCubic`, of finite-difference depth `2`, `3`.  The middle coefficient
(`11n²+11n+3`, `34n³−51n²+27n−5`), though the same degree, does not enter the Wronskian.
(This is a statement about the recurrence, carrying no irrationality claim — see
`DepthAperyCubic`.)

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

/-! ## §2 — telescoping the one-step law to a product (the `1/n³` Casoratian shape)

When the Casoratian is sign-definite (as it is for ζ(3): `c₀ = −(n−1)³`, so
`c₂(n)·Cₙ = (n−1)³·Cₙ₋₁` with every term `≥ 0`), its magnitude `g = |C|` obeys a single
multiplicative `ℕ` recurrence `P(n)·g(n) = Q(n)·g(n−1)` (here `P = c₂ = n³`, `Q = (n−1)³`).
This section telescopes that recurrence: the running products of `P` and `Q` carry `g(n)`
back to `g(0)`. -/

/-- `prodFrom f n = ∏_{k=1}^{n} f k` (empty product `1`). -/
def prodFrom (f : Nat → Nat) : Nat → Nat
  | 0   => 1
  | n+1 => prodFrom f n * f (n+1)

/-- ★★★ **Telescoping the multiplicative one-step law.**  If `g` obeys `P(n+1)·g(n+1) =
    Q(n+1)·g(n)` for all `n`, then `(∏_{k≤n} P k)·g(n) = (∏_{k≤n} Q k)·g(0)` — the running
    products of the outer coefficients carry the whole recurrence back to the start.  For the
    sign-definite ζ(3) Casoratian (`P = n³ = aperyTop`, `Q = (n−1)³ = aperyBot`,
    `g = |Cₙ|`) this is exactly `(∏ n³)·|Cₙ| = (∏ (n−1)³)·|C₀|` — the cube-product
    telescoping whose ratio is the `1/n³` denominator.  ∅-axiom, no signs. -/
theorem telescope (P Q g : Nat → Nat)
    (h : ∀ n, P (n+1) * g (n+1) = Q (n+1) * g n) :
    ∀ n, prodFrom P n * g n = prodFrom Q n * g 0
  | 0   => rfl
  | n+1 => by
      show prodFrom P n * P (n+1) * g (n+1) = prodFrom Q n * Q (n+1) * g 0
      rw [mul_assoc (prodFrom P n) (P (n+1)) (g (n+1)), h n,
          mul_left_comm (prodFrom P n) (Q (n+1)) (g n), telescope P Q g h n,
          mul_left_comm (Q (n+1)) (prodFrom Q n) (g 0),
          mul_assoc (prodFrom Q n) (Q (n+1)) (g 0)]

/-- A non-vacuous instance: the geometric magnitude `g(n) = rⁿ` solves the one-step law with
    `P = 1`, `Q = r` (`1·rⁿ⁺¹ = r·rⁿ`), and telescopes to `rⁿ = (∏ r)·1` — the
    escape-side reading (constant-`g` would be `P = Q`). -/
theorem telescope_geometric (r : Nat) (n : Nat) :
    prodFrom (fun _ => 1) n * r ^ n = prodFrom (fun _ => r) n * r ^ 0 :=
  telescope (fun _ => 1) (fun _ => r) (fun k => r ^ k)
    (fun m => by
      show 1 * r ^ (m+1) = r * r ^ m
      rw [Nat.one_mul, Nat.pow_succ, Nat.mul_comm (r ^ m) r]) n

end E213.Lib.Math.Cauchy.CasoratianStep
