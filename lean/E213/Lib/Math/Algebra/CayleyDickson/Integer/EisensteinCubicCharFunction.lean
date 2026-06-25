import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharOrthogonality
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharConj

/-!
# The cubic character as a `μ₃`-valued homomorphism `χ̂ : ℤ → μ₃` (∅-axiom)

The cubic character on the **cyclic exponent group** is the function `χ̂(i) = ωⁱ`.  On a primitive root
`g` (`a = gⁱ`) the cubic character `(a/d)₃ = ωⁱ` (up to the dlog identification), so `χ̂` packages the
multiplicative cubic character as a homomorphism `ℤ → μ₃`:

  * `chiExp_mul`    — `χ̂(i+j) = χ̂(i)·χ̂(j)`  (homomorphism)
  * `chiExp_period` — `χ̂(i+3) = χ̂(i)`        (order 3)
  * `chiExp_value`  — `χ̂(i) ∈ {1, ω, ω²}`     (`μ₃`-valued)
  * `chiExp_sum`    — `Σ_{i<3k} χ̂(i) = 0`     (character orthogonality)

with `geomSum_eq_sumRange` identifying the geometric sum with the generic `sumRange` (so the
orthogonality feeds the Jacobi-sum machinery).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFunction

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
  (pow one mul_one geomSum geomSum_zero geomSum_succ omega_pow_three)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sumRange_succ sum_mul_left sum_congr)
open E213.Meta.Algebra213.Ring213 (mul_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow_succ)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (pow_add)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega (char_omega_value)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharOrthogonality (geomSum_omega_three_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharConj (char_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)

/-- The cubic character on exponents: `χ̂(i) = ωⁱ`. -/
def chiExp (i : Nat) : ZOmega := pow Omega i

/-- ★★★ **Homomorphism** — `χ̂(i+j) = χ̂(i)·χ̂(j)` (`ω^{i+j} = ωⁱ·ωʲ`). -/
theorem chiExp_mul (i j : Nat) : chiExp (i + j) = chiExp i * chiExp j := pow_add Omega i j

/-- ★★★ **Order 3** — `χ̂(i+3) = χ̂(i)` (`ω³ = 1`). -/
theorem chiExp_period (i : Nat) : chiExp (i + 3) = chiExp i := by
  show pow Omega (i + 3) = pow Omega i
  rw [pow_add, omega_pow_three, mul_one]

/-- ★★★ **`μ₃`-valued** — `χ̂(i) ∈ {1, ω, ω²}`. -/
theorem chiExp_value (i : Nat) : chiExp i = one ∨ chiExp i = Omega ∨ chiExp i = Omega * Omega :=
  char_omega_value i

/-- `geomSum z n = Σ_{k<n} z^k` is the generic `sumRange` of the power sequence. -/
theorem geomSum_eq_sumRange (z : ZOmega) : ∀ n, geomSum z n = sumRange (fun k => pow z k) n
  | 0 => rfl
  | n + 1 => by rw [geomSum_succ, sumRange_succ, geomSum_eq_sumRange z n]

/-- ★★★★ **Character orthogonality** — `Σ_{i<3k} χ̂(i) = 0`: the cubic character summed over a full
    cycle vanishes (`geomSum_omega_three_mul` via `geomSum_eq_sumRange`). -/
theorem chiExp_sum (k : Nat) : sumRange chiExp (3 * k) = 0 := by
  show sumRange (fun i => pow Omega i) (3 * k) = 0
  rw [← geomSum_eq_sumRange]
  exact geomSum_omega_three_mul k

/-- **Power of a power** — `z^{a·b} = (z^a)^b`.  Induction on `b` with `pow_add`. -/
theorem pow_mul (z : ZOmega) (a : Nat) : ∀ b, pow z (a * b) = pow (pow z a) b
  | 0 => by rw [Nat.mul_zero]; rfl
  | b + 1 => by rw [Nat.mul_succ, pow_add, pow_mul z a b, pow_succ]

/-- ★★★ **The conjugate character is the square** — `conj χ̂(i) = χ̂(2i)`, i.e. `χ̄ = χ²` (`conj ω = ω²`).
    The standard relation between a cubic character and its conjugate, used in Jacobi-sum identities. -/
theorem chiExp_conj (i : Nat) : conj (chiExp i) = chiExp (2 * i) := by
  show conj (pow Omega i) = pow Omega (2 * i)
  rw [← char_conj Omega i, show conj Omega = pow Omega 2 from by decide, ← pow_mul]

/-- ★★★ **Character values have norm 1** — `‖ωⁱ‖² = 1` (`ω` is a unit, `‖ω‖²=1`).  Induction with
    norm-multiplicativity. -/
theorem pow_omega_norm_one : ∀ i, (pow Omega i).normSq = 1
  | 0 => by decide
  | i + 1 => by
      show (pow Omega i * Omega).normSq = 1
      rw [normSq_mul, pow_omega_norm_one i, show Omega.normSq = 1 from by decide, Int.one_mul]

/-- ★★★ **Character values are units** — `χ̂(i) · conj χ̂(i) = 1` (the `|χ(t)| = 1` metric, behind
    `|J(χ,χ)|² = p`).  From `mul_conj_self` and `pow_omega_norm_one`. -/
theorem chiExp_unit (i : Nat) : chiExp i * conj (chiExp i) = one := by
  show pow Omega i * (pow Omega i).conj = one
  rw [mul_conj_self, pow_omega_norm_one]; rfl

/-- ★★★★ **Translation invariance of the character sum** — `Σ_{i<3k} χ̂(c+i) = 0`.  The orthogonality
    is unchanged by an exponent shift: `χ̂(c+i) = χ̂(c)·χ̂(i)` factors `χ̂(c)` out, and `Σ χ̂(i) = 0`.
    A Jacobi-sum manipulation tool. -/
theorem chiExp_sum_shift (c k : Nat) : sumRange (fun i => chiExp (c + i)) (3 * k) = 0 := by
  rw [sum_congr (3 * k) (fun i _ => chiExp_mul c i), sum_mul_left, chiExp_sum, mul_zero]

/-- ★★★ **Diagonal Schur orthogonality** — `Σ_{i<n} χ̂(i)·conj χ̂(i) = Σ_{i<n} 1` (each term is the
    unit norm `1`); the character against its own conjugate sums to the count.  Complements the
    off-diagonal `Σ χ̂ = 0` (`chiExp_sum`). -/
theorem chiExp_diag_sum (n : Nat) :
    sumRange (fun i => chiExp i * conj (chiExp i)) n = sumRange (fun _ => one) n :=
  sum_congr n (fun i _ => chiExp_unit i)

/-- ★★★★★ **The cubic character is a nontrivial order-3 character with vanishing sum.**  Bundles the
    defining properties of `χ̂(i) = ωⁱ`: it is a homomorphism, has order 3, is nontrivial, and sums to
    zero over a full cycle — i.e. a genuine nontrivial multiplicative character of order 3 obeying the
    orthogonality relation.  ∅-axiom. -/
theorem cubic_character_summary :
    (∀ i j, chiExp (i + j) = chiExp i * chiExp j) ∧
    (∀ i, chiExp (i + 3) = chiExp i) ∧
    chiExp 1 ≠ one ∧
    (∀ k, sumRange chiExp (3 * k) = 0) :=
  ⟨chiExp_mul, chiExp_period, by decide, chiExp_sum⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFunction
