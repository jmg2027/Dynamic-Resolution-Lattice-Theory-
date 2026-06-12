import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Meta.Nat.PolyNatMTactic

/-!
# AperyIntegrality — Brick 2 (Apéry integrality, ζ(3) input I1), ∅-axiom

The integrality `2·lcm(1..n)³·aₙ ∈ ℕ` of the reduced Apéry numerators, as pure
divisibility chains (no `ord_p`, no Legendre, no primes — the heart collapses to
exact cofactor equations).

  * **§1 — the trinomial double identity** (`aperyTrinomial`): in the
    subtraction-free additive parametrisation `n = m+a+b`, `k = m+b`,
    `C(n,k)·C(n+k,k)·C(k,m)² = C(n,m)·C(n+m,m)·C(n−m,k−m)·C(n+k,n+m)`.  Both sides
    clear to `(2m+a+2b)! / (a!·(m!)²·(b!)²)`.
  * **§2 — KeyDiv** (in progress): `m·C(k,m) ∣ lcm(1..k)`, via the finite-difference
    identity `Σⱼ(−1)ʲC(s,j)·Πᵢ≠ⱼ(m+i) = s!`.  Foundations here: the rising
    factorial `rprod`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AperyIntegrality

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_pos
  factorial_succ)
open E213.Tactic.NatHelper (sub_add_cancel add_right_cancel)

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

/-! ## §2 — KeyDiv foundations: the rising factorial -/

/-- Rising factorial `(m)(m+1)···(m+len−1)`, `len` factors (`rprod m 0 = 1`). -/
def rprod (m : Nat) : Nat → Nat
  | 0 => 1
  | len + 1 => rprod m len * (m + len)

/-- Back factor: `rprod m (len+1) = rprod m len · (m+len)`. -/
theorem rprod_back (m len : Nat) : rprod m (len + 1) = rprod m len * (m + len) := rfl

/-- Front factor: `rprod m (len+1) = m · rprod (m+1) len`. -/
theorem rprod_front (m : Nat) : ∀ len, rprod m (len + 1) = m * rprod (m + 1) len
  | 0 => by show 1 * (m + 0) = m * 1; rw [Nat.one_mul, Nat.add_zero, Nat.mul_one]
  | len + 1 => by
      show rprod m (len + 1) * (m + (len + 1)) = m * (rprod (m + 1) len * (m + 1 + len))
      rw [rprod_front m len, show m + (len + 1) = m + 1 + len from by ring_nat]
      ring_nat

/-- `rprod 1 len = len!`. -/
theorem rprod_one (len : Nat) : rprod 1 len = factorial len := by
  induction len with
  | zero => rfl
  | succ len ih => rw [rprod_back, ih, factorial_succ, Nat.add_comm 1 len, Nat.mul_comm]

/-- `rprod m len > 0` when `m ≥ 1` (every factor `m+i ≥ 1`). -/
theorem rprod_pos {m : Nat} (hm : 1 ≤ m) : ∀ len, 0 < rprod m len
  | 0 => Nat.zero_lt_one
  | len + 1 => Nat.mul_pos (rprod_pos hm len) (Nat.le_trans hm (Nat.le_add_right m len))

/-- Pure `(s+1) − j = (s−j) + 1` for `j ≤ s` (`Nat.succ_sub` carries `propext`). -/
private theorem succ_sub_pure {s j : Nat} (hj : j ≤ s) : (s + 1) - j = (s - j) + 1 := by
  have e1 : ((s - j) + 1) + j = s + 1 := by rw [Nat.add_right_comm, sub_add_cancel hj]
  have e2 : ((s + 1) - j) + j = s + 1 := sub_add_cancel (Nat.le_succ_of_le hj)
  exact add_right_cancel (e2.trans e1.symm)

/-- The product `Π_{i∈[0,s], i≠j}(m+i)` (meaningful for `j ≤ s`). -/
def Qex (m s j : Nat) : Nat := rprod m j * rprod (m + j + 1) (s - j)

/-- Back recurrence: extending the range by `m+s+1`.  `Qex m (s+1) j = (m+s+1)·Qex m s j`
    for `j ≤ s` (the new factor `m+s+1` joins the product). -/
theorem Qex_back {s j : Nat} (hj : j ≤ s) (m : Nat) :
    Qex m (s + 1) j = (m + s + 1) * Qex m s j := by
  show rprod m j * rprod (m + j + 1) ((s + 1) - j)
    = (m + s + 1) * (rprod m j * rprod (m + j + 1) (s - j))
  rw [succ_sub_pure hj, rprod_back,
      show m + j + 1 + (s - j) = m + s + 1 from by
        rw [show m + j + 1 + (s - j) = (m + 1) + (j + (s - j)) from by ring_nat,
            Nat.add_comm j (s - j), sub_add_cancel hj]; ring_nat]
  ring_nat

/-- Front recurrence: peeling the first factor `m`.  `Qex m (s+1) (j+1) = m·Qex (m+1) s j`. -/
theorem Qex_front (m s j : Nat) : Qex m (s + 1) (j + 1) = m * Qex (m + 1) s j := by
  show rprod m (j + 1) * rprod (m + (j + 1) + 1) ((s + 1) - (j + 1))
    = m * (rprod (m + 1) j * rprod (m + 1 + j + 1) (s - j))
  rw [rprod_front m j, Nat.succ_sub_succ, show m + (j + 1) + 1 = m + 1 + j + 1 from by ring_nat]
  ring_nat

end E213.Lib.Math.NumberTheory.AperyIntegrality
