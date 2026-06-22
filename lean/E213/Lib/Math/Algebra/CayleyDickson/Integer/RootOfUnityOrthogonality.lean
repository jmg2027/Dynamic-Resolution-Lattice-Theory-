import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaUnits
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaAlgebra213

/-!
# RootOfUnityOrthogonality — additive character orthogonality `Σ ζᵏ = 0` (∅-axiom)

The **general order-`d` leg** of the character-orthogonality target located in
`research-notes/decomposition/practice/fourier.md`.  The order-2 (Legendre) case
was closed in `ModArith/CharacterOrthogonality.quadratic_orthogonality` via the
`(−1)^k` parity telescope.  Orders `> 2` were placed in the `Real213`/cyclotomic
"transcendental-cut residue": a primitive `n`-th root of unity `ζ` for `n > 2`
was claimed to be unavailable as a finite combinatorial object.

That boundary is **partially relocated** here.  The Eisenstein integers `ℤ[ω]`
(`ZOmega`, `ω² + ω + 1 = 0`) are a *concrete, decidable, ∅-axiom* commutative
ring (`ZOmegaAlgebra213`) that already **contains** roots of unity of orders
`3` and `6`:

  * `ω = ⟨0,1⟩` is a primitive **cube** root of unity (`ZOmegaUnits.omega_cubed_eq_one`).
  * `ζ₆ = 1 + ω = ⟨1,1⟩` is a primitive **6th** root (`ZOmegaUnits.zeta6_pow_six`).

So the additive-character orthogonality `Σ_{k=0}^{n-1} ζᵏ = 0` is, for these `n`,
a finite integer identity — provable with no analysis and no transcendental cut.

## The technique that pays off — the geometric telescope

The single algebraic engine, generic over the ring (`geomSum_telescope`):

> `(ζ − 1) · Σ_{k=0}^{n−1} ζᵏ = ζⁿ − 1`.

When `ζⁿ = 1` the right side is `0`, so `(ζ − 1) · Σ = 0`; and since `ℤ[ω]` is an
integral domain and `ζ ≠ 1`, `Σ = 0`.  This is the order-`d` generalisation of the
order-2 `+1, −1` pair-cancellation: the same telescoping `× resolution` the note
predicted, now for `n = 3, 6`.

  * ★★★ `geomSum_telescope`     — `(ζ−1)·Σ_{k<n} ζᵏ = ζⁿ − 1` (generic, by induction).
  * ★★★ `omega_orthogonality`   — `1 + ω + ω² = 0` (order-3 character sum).
  * ★★★ `zeta6_orthogonality`   — `Σ_{k=0}^{5} ζ₆ᵏ = 0` (order-6 character sum).
  * ★★★★ `root_orthogonality`   — for any `ζ : ZOmega` with `ζⁿ = 1`,
    `(ζ−1)·geomSum ζ n = 0`; the orthogonality defect lives entirely in `(ζ−1)`.

All ∅-axiom (`#print axioms` clean).

This **partially closes** fourier.md's general-χ target: the *additive*
orthogonality `Σ ζᵏ = 0` is now machine-checked for the concrete cyclotomic
orders `3, 6` realised in `ℤ[ω]` — not only order `2`.  It does NOT close the
*arbitrary*-`n` case (a general primitive `n`-th root for `n ∉ {1,2,3,4,6}` is
not an Eisenstein/Gaussian integer; those `ζ` remain `Real213` cuts).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Meta.Algebra213 (Ring213)

/-! ## §0 — `ZOmega` ring facts used by the telescope (kept local, ∅-axiom) -/

/-- `u + v = v + u`. -/
theorem add_comm_zomega (u v : ZOmega) : u + v = v + u := by
  apply ext
  · exact E213.Meta.Int213.add_comm _ _
  · exact E213.Meta.Int213.add_comm _ _

/-- `u + v + w = u + (v + w)`. -/
theorem add_assoc_zomega (u v w : ZOmega) : u + v + w = u + (v + w) := by
  apply ext
  · exact E213.Meta.Int213.add_assoc _ _ _
  · exact E213.Meta.Int213.add_assoc _ _ _

/-- `u + 0 = u`. -/
theorem add_zero_zomega (u : ZOmega) : u + 0 = u := by
  apply ext
  · show u.re + 0 = u.re; exact Int.add_zero _
  · show u.im + 0 = u.im; exact Int.add_zero _

/-- `-u + u = 0`. -/
theorem add_left_neg_zomega (u : ZOmega) : -u + u = 0 := by
  apply ext
  · exact E213.Meta.Int213.add_left_neg _
  · exact E213.Meta.Int213.add_left_neg _

/-- `u + -u = 0`. -/
theorem add_right_neg_zomega (u : ZOmega) : u + (-u) = 0 := by
  rw [add_comm_zomega]; exact add_left_neg_zomega u

/-- `u − u = 0`. -/
theorem sub_self_zomega (u : ZOmega) : u - u = 0 := by
  show u + (-u) = 0
  exact add_right_neg_zomega u

/-- `u · 0 = 0` in ZOmega. -/
theorem mul_zero_zomega (u : ZOmega) : u * (0 : ZOmega) = 0 := by
  apply ext
  · show u.re * 0 - u.im * 0 = 0
    rw [E213.Meta.Int213.mul_comm u.re 0, E213.Meta.Int213.mul_comm u.im 0,
        E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul,
        Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  · show u.re * 0 + u.im * 0 - u.im * 0 = 0
    rw [E213.Meta.Int213.mul_comm u.re 0, E213.Meta.Int213.mul_comm u.im 0,
        E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul,
        Int.add_zero, Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]

/-- `(-u)·w = -(u·w)`. -/
theorem neg_mul_zomega (u w : ZOmega) : (-u) * w = -(u * w) := by
  apply ext
  · show (-u.re) * w.re - (-u.im) * w.im = -(u.re * w.re - u.im * w.im)
    rw [E213.Meta.Int213.neg_mul, E213.Meta.Int213.neg_mul,
        Int.sub_eq_add_neg, Int.sub_eq_add_neg, E213.Meta.Int213.neg_add,
        Int.neg_neg]
  · show (-u.re) * w.im + (-u.im) * w.re - (-u.im) * w.im
       = -(u.re * w.im + u.im * w.re - u.im * w.im)
    rw [E213.Meta.Int213.neg_mul, E213.Meta.Int213.neg_mul,
        E213.Meta.Int213.neg_mul, Int.sub_eq_add_neg, Int.sub_eq_add_neg,
        Int.neg_neg, E213.Meta.Int213.neg_add, E213.Meta.Int213.neg_add,
        Int.neg_neg]

/-- `(u − v)·w = u·w − v·w` in ZOmega. -/
theorem sub_mul_zomega (u v w : ZOmega) : (u - v) * w = u * w - v * w := by
  show (u + (-v)) * w = u * w + (-(v * w))
  rw [Ring213.add_mul u (-v) w, neg_mul_zomega v w]

/-! ## §1 — the multiplicative unit and powers in `ZOmega` -/

/-- The ring unit `1 = ⟨1,0⟩ = ofInt 1`. -/
def one : ZOmega := ⟨1, 0⟩

/-- `1 · u = u`.  Direct from the `mul` formula with `re = 1, im = 0`. -/
theorem one_mul (u : ZOmega) : one * u = u := by
  apply ext
  · show (1 : Int) * u.re - 0 * u.im = u.re
    rw [E213.Meta.Int213.zero_mul, Int.one_mul,
        Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  · show (1 : Int) * u.im + 0 * u.re - 0 * u.im = u.im
    rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul, Int.one_mul,
        Int.add_zero, Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]

/-- `u · 1 = u`. -/
theorem mul_one (u : ZOmega) : u * one = u := by
  rw [ZOmega.mul_comm]; exact one_mul u

/-- Bare power `ζ^n` (left fold), `ζ^0 = 1`. -/
def pow (z : ZOmega) : Nat → ZOmega
  | 0     => one
  | n + 1 => pow z n * z

@[simp] theorem pow_zero (z : ZOmega) : pow z 0 = one := rfl
theorem pow_succ (z : ZOmega) (n : Nat) : pow z (n + 1) = pow z n * z := rfl

/-! ## §2 — the partial geometric sum and the telescope identity -/

/-- The partial sum `Σ_{k=0}^{n-1} ζᵏ`. -/
def geomSum (z : ZOmega) : Nat → ZOmega
  | 0     => 0
  | n + 1 => geomSum z n + pow z n

@[simp] theorem geomSum_zero (z : ZOmega) : geomSum z 0 = 0 := rfl
theorem geomSum_succ (z : ZOmega) (n : Nat) :
    geomSum z (n + 1) = geomSum z n + pow z n := rfl

/-- The single induction-step ring identity (writing `p = zⁿ`):
    `(p − 1) + (z − 1)·p = p·z − 1`. -/
theorem telescope_step (p z : ZOmega) :
    (p - one) + (z - one) * p = p * z - one := by
  -- (z−1)·p = z·p − p = p·z − p (commutative)
  rw [show (z - one) * p = z * p - one * p from sub_mul_zomega z one p,
      one_mul p, ZOmega.mul_comm z p]
  -- goal: (p + -1) + (p·z + -p) = p·z + -1
  show (p + (-one)) + (p * z + (-p)) = p * z + (-one)
  rw [add_assoc_zomega p (-one) (p * z + (-p))]
  rw [← add_assoc_zomega (-one) (p * z) (-p)]
  rw [add_comm_zomega (-one) (p * z)]
  rw [add_assoc_zomega (p * z) (-one) (-p)]
  rw [add_comm_zomega (-one) (-p)]
  rw [← add_assoc_zomega (p * z) (-p) (-one)]
  rw [← add_assoc_zomega p (p * z + -p) (-one)]
  rw [← add_assoc_zomega p (p * z) (-p)]
  rw [add_comm_zomega p (p * z)]
  rw [add_assoc_zomega (p * z) p (-p)]
  rw [add_right_neg_zomega p, add_zero_zomega (p * z)]

/-- ★★★ **The geometric telescope** — generic over the ring.

    `(ζ − 1) · Σ_{k=0}^{n−1} ζᵏ = ζⁿ − 1`.

    Proof by induction on `n`: the `n+1` step adds `(ζ−1)·ζⁿ = ζⁿ⁺¹ − ζⁿ` to the
    inductive `ζⁿ − 1`; the `−ζⁿ` and `+ζⁿ` cancel, leaving `ζⁿ⁺¹ − 1`.  This is
    the single algebraic engine behind every order's orthogonality — the order-`d`
    generalisation of the order-2 `+1,−1` pair telescope. -/
theorem geomSum_telescope (z : ZOmega) :
    ∀ n, (z - one) * geomSum z n = pow z n - one
  | 0     => by
    show (z - one) * 0 = one - one
    rw [mul_zero_zomega (z - one)]
    exact (sub_self_zomega one).symm
  | n + 1 => by
    rw [geomSum_succ, Ring213.mul_add, geomSum_telescope z n, pow_succ]
    -- goal: (pow z n - one) + (z - one) * pow z n = pow z n * z - one
    exact telescope_step (pow z n) z

/-! ## §3 — concrete orthogonality at the cyclotomic orders 3 and 6 -/

/-- ★★★ **Order-3 orthogonality.**  `1 + ω + ω² = 0` — the sum of all three cube
    roots of unity vanishes.  This is the additive-character orthogonality at the
    primitive cube root `ω`, the order-3 analogue of `1 + (−1) = 0`. -/
theorem omega_orthogonality : geomSum Omega 3 = 0 := by decide

/-- ★★★ **Order-6 orthogonality.**  `Σ_{k=0}^{5} ζ₆ᵏ = 0` for `ζ₆ = 1 + ω = ⟨1,1⟩`,
    the primitive 6th root of unity in `ℤ[ω]`. -/
theorem zeta6_orthogonality : geomSum Zeta6 6 = 0 := by decide

/-! ## §4 — the structural form: orthogonality defect lives in `(ζ − 1)` -/

/-- ★★★★ **Root-of-unity orthogonality, structural form.**  For *any* `ζ : ZOmega`
    that is an `n`-th root of unity (`ζⁿ = 1`), the geometric sum is annihilated by
    `ζ − 1`:

      `(ζ − 1) · Σ_{k=0}^{n−1} ζᵏ = 0`.

    Immediate from `geomSum_telescope` once `pow z n = 1`.  Since `ℤ[ω]` is an
    integral domain, a *primitive* root (`ζ ≠ 1`) forces `Σ = 0` — exactly the
    character orthogonality, with the whole defect carried by the factor `ζ − 1`. -/
theorem root_orthogonality (z : ZOmega) (n : Nat) (hz : pow z n = one) :
    (z - one) * geomSum z n = 0 := by
  rw [geomSum_telescope z n, hz]
  exact sub_self_zomega one

/-- ★★★ `ω³ = 1` in the `pow` notation (bridges `ZOmegaUnits.omega_cubed_eq_one`). -/
theorem omega_pow_three : pow Omega 3 = one := by decide

/-- ★★★ `ζ₆⁶ = 1` in the `pow` notation (bridges `ZOmegaUnits.zeta6_pow_six`). -/
theorem zeta6_pow_six' : pow Zeta6 6 = one := by decide

/-- ★★★★★ **Capstone — additive character orthogonality at orders 3 and 6.**

    Both the cube root `ω` and the 6th root `ζ₆` satisfy `ζⁿ = 1` and
    `Σ_{k<n} ζᵏ = 0`, with the telescope `(ζ−1)·Σ = ζⁿ−1 = 0` as the common
    mechanism.  This is the order-`d` (`d > 2`) generalisation of the Legendre
    (`d = 2`) orthogonality `quadratic_orthogonality`, realised concretely in the
    Eisenstein ring `ℤ[ω]` with no transcendental cut. -/
theorem cyclotomic_orthogonality :
    (pow Omega 3 = one ∧ geomSum Omega 3 = 0) ∧
    (pow Zeta6 6 = one ∧ geomSum Zeta6 6 = 0) ∧
    (∀ z : ZOmega, ∀ n, pow z n = one → (z - one) * geomSum z n = 0) :=
  ⟨⟨omega_pow_three, omega_orthogonality⟩,
   ⟨zeta6_pow_six', zeta6_orthogonality⟩,
   root_orthogonality⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
