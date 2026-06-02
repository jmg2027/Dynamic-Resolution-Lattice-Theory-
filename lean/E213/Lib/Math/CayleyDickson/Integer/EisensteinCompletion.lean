import E213.Lib.Math.CayleyDickson.Integer.EisensteinCrossDet
import E213.Lib.Math.Real213.ContinuedFractionModulus

/-!
# EisensteinCompletion — the 3-axis continued fraction: floor rotation + completion

`EisensteinCrossDet` closed the **floor**: the cross-determinant of `ℤ[ω]`-convergents
rides the 6-unit group (`crossDet_on_units`).  This file develops the **completion** —
when do the convergents actually converge? — and finds the answer factors through the
2-axis (real) growth.

  * ★★ `gap_scale_factors` — the convergent gap `p_{n+1}/q_{n+1} − p_n/q_n = W_n/(q_n q_{n+1})`
    has unit numerator (`‖W_n‖² = 1`, the floor), so its scale is the **integer** norm
    product `‖q_n‖²·‖q_{n+1}‖² = ‖q_n q_{n+1}‖²` (`normSq_mul`).  Eisenstein (3-axis)
    convergence is governed entirely by the growth of the integer norm sequence
    `N_n = ‖q_n‖²` — a 2-axis quantity.
  * ★★★ `eisenstein_real_slice_completes` — the real partial-quotient slice (`a_i ∈ ℤ ⊂
    ℤ[ω]`) embeds: the Eisenstein convergent denominators are real, their norms are the
    **squares** of the real continued-fraction denominators (`cfQn`), which diverge
    (`cfQn_ge_self`).  So every real's Eisenstein continued fraction completes through its
    real completion (`Real213.ContinuedFractionModulus.cf_universal_total_modulus`) — the
    2-axis is the completing diagonal inside the 3-axis.
  * ★★★ `eisenstein_floor_rotation` — the genuinely-complex content: the cross-determinant
    floor **rotates** by the fixed primitive 6th root `μ = ⟨0,−1⟩ = −ω`
    (`omega_cross_step`), with order `6 = NS·NT` (`μ⁶ = 1`), the orbit returning at step
    `6`.  Over `ℤ` the rotation is by `−1` (order `2`); over the hexagonal `ℤ[ω]` it is
    order `6`.  The floor's rotation order **is** the unit-group order **is** `NS·NT`.

The 3-axis is richer than the 2-axis in exactly one way — the floor's rotation order
(`6` vs `2`) — while convergence itself is a 2-axis phenomenon: the integer norm sequence
must grow, and on the real slice it grows as a perfect square.

All zero-axiom.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.EisensteinCompletion

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.EisensteinCrossDet
open E213.Lib.Math.Real213.ContinuedFractionFloor (cfQn cfQn_pos)
open E213.Lib.Math.Real213.ContinuedFractionModulus (cfPn cfQn_ge_self)

/-! ## §1 — the gap scale factors into the integer norm product -/

/-- ★★ **The Eisenstein convergent gap scale is the integer norm product.**  The gap
    `W_n/(q_n q_{n+1})` has unit numerator (the floor `‖W_n‖² = 1`), so its size² is
    `1/‖q_n q_{n+1}‖² = 1/(‖q_n‖²·‖q_{n+1}‖²)` — a purely 2-axis (integer) quantity. -/
theorem gap_scale_factors (d : Nat → ZOmega) (n : Nat) :
    (d n * d (n+1)).normSq = (d n).normSq * (d (n+1)).normSq :=
  ZOmega.normSq_mul (d n) (d (n+1))

/-! ## §2 — the real slice completes (the 2-axis diagonal) -/

/-- The Eisenstein convergent denominators of a real partial-quotient sequence. -/
def dEis (a : Nat → Nat) (n : Nat) : ZOmega := ZOmega.ofInt (cfQn a n)

/-- The Eisenstein convergent numerators of a real partial-quotient sequence. -/
def aEis (a : Nat → Nat) (n : Nat) : ZOmega := ZOmega.ofInt (cfPn a n)

/-- `‖ofInt k‖² = k²`: the real slice's norm is a perfect square. -/
theorem ofInt_normSq (k : Int) : (ZOmega.ofInt k).normSq = k * k := by
  show k * k - k * 0 + 0 * 0 = k * k
  rw [Int.mul_zero, Int.mul_zero]
  exact E213.Meta.Int213.sub_add_cancel_int (k * k) 0

/-- The real-slice Eisenstein denominator norm is the **square** of the real
    continued-fraction denominator `cfQn`. -/
theorem dEis_normSq (a : Nat → Nat) (n : Nat) :
    (dEis a n).normSq = (cfQn a n : Int) * (cfQn a n : Int) :=
  ofInt_normSq _

/-- ★★ **The real-slice denominator norms diverge.**  `‖q_n‖² = (cfQn n)² ≥ n²`, so for
    any bound `K` the norms eventually exceed it — the convergent gaps shrink to zero, the
    Eisenstein continued fraction of a real number is Cauchy. -/
theorem dEis_norm_diverges (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) (K : Nat) :
    ∃ N, ∀ n, N ≤ n → K ≤ cfQn a n * cfQn a n := by
  refine ⟨K, ?_⟩
  intro n hn
  have hK : K ≤ cfQn a n := Nat.le_trans hn (cfQn_ge_self a ha n)
  have h1 : 1 ≤ cfQn a n := cfQn_pos a ha n
  calc K = K * 1 := (Nat.mul_one K).symm
    _ ≤ cfQn a n * cfQn a n := Nat.mul_le_mul hK h1

/-- ★★★ **The real slice of the Eisenstein continued fraction completes.**  For any real
    `≥ 1` (partial quotients `≥ 1`), the Eisenstein convergent denominators have norm equal
    to the square of the real denominator, and those norms diverge — so the gaps (unit
    numerator over diverging norm) shrink to zero.  The cut-level completion is
    `Real213.ContinuedFractionModulus.cf_universal_total_modulus`; here is the Eisenstein
    norm half: the 2-axis is the completing diagonal of the 3-axis. -/
theorem eisenstein_real_slice_completes (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) :
    (∀ n, (dEis a n).normSq = (cfQn a n : Int) * (cfQn a n : Int))
    ∧ (∀ K, ∃ N, ∀ n, N ≤ n → K ≤ cfQn a n * cfQn a n) :=
  ⟨dEis_normSq a, dEis_norm_diverges a ha⟩

/-! ## §3 — the floor rotation (the genuinely-complex content) -/

/-- **The cross-determinant rotation step.**  For the ω-Fibonacci convergents the
    cross-determinant is multiplied each step by the fixed `μ = ⟨0,−1⟩ = −ω`, a primitive
    6th root of unity. -/
theorem omega_cross_step (n : Nat) :
    crossDet aFib dFib (n+1) = (⟨0, -1⟩ : ZOmega) * crossDet aFib dFib n := by
  rw [crossDet_step aFib dFib (ZOmega.ofInt 1) ZOmega.Omega
        (fun m => efib_rec (ZOmega.ofInt 1) ZOmega.Omega 0 (ZOmega.ofInt 1) m)
        (fun m => efib_rec (ZOmega.ofInt 1) ZOmega.Omega (ZOmega.ofInt 1) 0 m) n,
      show (⟨0, -1⟩ : ZOmega) = -ZOmega.Omega from by decide,
      E213.Meta.Algebra213.Ring213.neg_mul]

/-- ★★★ **The floor rotates with order `6 = NS·NT`.**  The cross-determinant is multiplied
    each step by the fixed primitive 6th root `μ = −ω` (`omega_cross_step`), `μ⁶ = 1`, the
    orbit returning at step `6`; the unit group it walks has order `6 = NS·NT`.  Over `ℤ`
    the analogous rotation is by `−1` (order `2`); the hexagonal `ℤ[ω]` lifts it to order
    `6`.  The 3-axis floor's rotation order is the unit-group order. -/
theorem eisenstein_floor_rotation :
    (∀ n, crossDet aFib dFib (n+1) = (⟨0, -1⟩ : ZOmega) * crossDet aFib dFib n)
    ∧ ((⟨0, -1⟩ : ZOmega) * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩
        = ZOmega.ofInt 1)
    ∧ (crossDet aFib dFib 6 = crossDet aFib dFib 0)
    ∧ units6.length = 6 :=
  ⟨omega_cross_step, by decide, by decide, units6_length⟩

end E213.Lib.Math.CayleyDickson.Integer.EisensteinCompletion
