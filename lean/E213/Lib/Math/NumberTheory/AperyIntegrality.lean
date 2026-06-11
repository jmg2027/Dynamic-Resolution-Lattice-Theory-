import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Meta.Nat.PolyNatMTactic

/-!
# AperyIntegrality — Brick 2 (Apéry integrality, ζ(3) input I1), ∅-axiom

The integrality `2·lcm(1..n)³·aₙ ∈ ℕ` of the reduced Apéry numerators, as pure
divisibility chains (no `ord_p`, no Legendre, no primes — the heart collapses to
exact cofactor equations).

  * **§1 — the trinomial double identity** (this file): in the subtraction-free
    additive parametrisation `n = m+a+b`, `k = m+b` (so `n−k = a`, `k−m = b`),
    `C(n,k)·C(n+k,k)·C(k,m)² = C(n,m)·C(n+m,m)·C(n−m,k−m)·C(n+k,n+m)`, i.e.
    `aperyTrinomial`.  Both sides clear to `(2m+a+2b)! / (a!·(m!)²·(b!)²)` — proved
    by telescoping `choose_mul_factorials` and cancelling.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AperyIntegrality

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_pos)

/-! ## §1 — the trinomial double identity -/

/-- The left side cleared by `a!·(m!)²·(b!)²` telescopes to `(2m+a+2b)!`. -/
private theorem lhs_clear (m a b : Nat) :
    (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)
        * (choose (m + b) m * choose (m + b) m))
      * (factorial a * factorial m * factorial m * factorial b * factorial b)
    = factorial (2 * m + a + 2 * b) := by
  have id1 : choose (m + b) m * (factorial m * factorial b) = factorial (m + b) :=
    choose_mul_factorials m b
  have id2 : choose (m + a + b) (m + b) * (factorial (m + b) * factorial a)
      = factorial (m + a + b) := by
    have h := choose_mul_factorials (m + b) a
    rwa [show m + b + a = m + a + b from by ring_nat] at h
  have id3 : choose (2 * m + a + 2 * b) (m + b) * (factorial (m + b) * factorial (m + a + b))
      = factorial (2 * m + a + 2 * b) := by
    have h := choose_mul_factorials (m + b) (m + a + b)
    rwa [show m + b + (m + a + b) = 2 * m + a + 2 * b from by ring_nat] at h
  calc (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)
          * (choose (m + b) m * choose (m + b) m))
        * (factorial a * factorial m * factorial m * factorial b * factorial b)
      = choose (2 * m + a + 2 * b) (m + b) * (choose (m + a + b) (m + b)
          * (choose (m + b) m * (factorial m * factorial b))
          * (choose (m + b) m * (factorial m * factorial b)) * factorial a) := by ring_nat
    _ = choose (2 * m + a + 2 * b) (m + b)
          * (choose (m + a + b) (m + b) * factorial (m + b) * factorial (m + b) * factorial a) := by
        rw [id1]
    _ = choose (2 * m + a + 2 * b) (m + b)
          * (factorial (m + b) * (choose (m + a + b) (m + b) * (factorial (m + b) * factorial a))) := by
        ring_nat
    _ = choose (2 * m + a + 2 * b) (m + b) * (factorial (m + b) * factorial (m + a + b)) := by
        rw [id2]
    _ = factorial (2 * m + a + 2 * b) := id3

/-- The right side cleared by `a!·(m!)²·(b!)²` telescopes to `(2m+a+2b)!`. -/
private theorem rhs_clear (m a b : Nat) :
    (choose (m + a + b) m * choose (2 * m + a + b) m * choose (a + b) b
        * choose (2 * m + a + 2 * b) (2 * m + a + b))
      * (factorial a * factorial m * factorial m * factorial b * factorial b)
    = factorial (2 * m + a + 2 * b) := by
  have id1 : choose (a + b) b * (factorial b * factorial a) = factorial (a + b) := by
    have h := choose_mul_factorials b a
    rwa [show b + a = a + b from by ring_nat] at h
  have id2 : choose (m + a + b) m * (factorial m * factorial (a + b)) = factorial (m + a + b) := by
    have h := choose_mul_factorials m (a + b)
    rwa [show m + (a + b) = m + a + b from by ring_nat] at h
  have id3 : choose (2 * m + a + b) m * (factorial m * factorial (m + a + b))
      = factorial (2 * m + a + b) := by
    have h := choose_mul_factorials m (m + a + b)
    rwa [show m + (m + a + b) = 2 * m + a + b from by ring_nat] at h
  have id4 : choose (2 * m + a + 2 * b) (2 * m + a + b)
      * (factorial (2 * m + a + b) * factorial b) = factorial (2 * m + a + 2 * b) := by
    have h := choose_mul_factorials (2 * m + a + b) b
    rwa [show 2 * m + a + b + b = 2 * m + a + 2 * b from by ring_nat] at h
  calc (choose (m + a + b) m * choose (2 * m + a + b) m * choose (a + b) b
          * choose (2 * m + a + 2 * b) (2 * m + a + b))
        * (factorial a * factorial m * factorial m * factorial b * factorial b)
      = choose (m + a + b) m * choose (2 * m + a + b) m
          * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (choose (a + b) b * (factorial b * factorial a)) * factorial m * factorial m
          * factorial b := by ring_nat
    _ = choose (m + a + b) m * choose (2 * m + a + b) m
          * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * factorial (a + b) * factorial m * factorial m * factorial b := by rw [id1]
    _ = choose (2 * m + a + b) m * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (choose (m + a + b) m * (factorial m * factorial (a + b))) * factorial m
          * factorial b := by ring_nat
    _ = choose (2 * m + a + b) m * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * factorial (m + a + b) * factorial m * factorial b := by rw [id2]
    _ = choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (choose (2 * m + a + b) m * (factorial m * factorial (m + a + b))) * factorial b := by
        ring_nat
    _ = choose (2 * m + a + 2 * b) (2 * m + a + b) * factorial (2 * m + a + b) * factorial b := by
        rw [id3]
    _ = choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (factorial (2 * m + a + b) * factorial b) := by ring_nat
    _ = factorial (2 * m + a + 2 * b) := id4

/-- ★★★ **The trinomial double identity** (Brick 2 step 1), additive form
    `n = m+a+b`, `k = m+b`: `C(n,k)·C(n+k,k)·C(k,m)² = C(n,m)·C(n+m,m)·C(n−m,k−m)·
    C(n+k,n+m)`.  Both sides clear by `a!·(m!)²·(b!)²` to `(2m+a+2b)!`. -/
theorem aperyTrinomial (m a b : Nat) :
    choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)
        * (choose (m + b) m * choose (m + b) m)
    = choose (m + a + b) m * choose (2 * m + a + b) m * choose (a + b) b
        * choose (2 * m + a + 2 * b) (2 * m + a + b) := by
  have hD : 0 < factorial a * factorial m * factorial m * factorial b * factorial b :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos a) (factorial_pos m))
      (factorial_pos m)) (factorial_pos b)) (factorial_pos b)
  exact Nat.eq_of_mul_eq_mul_right hD ((lhs_clear m a b).trans (rhs_clear m a b).symm)

end E213.Lib.Math.NumberTheory.AperyIntegrality
