import E213.Lib.Math.Mobius213.Px.QFibIdentity
import E213.Lib.Math.Real213.PhiAsCut
import E213.Meta.Nat.PureNat
import E213.Lib.Math.NatRing

/-!
# FibCassiniNat — the Fibonacci convergents lie below φ (all-Nat, ∀ n)

The φ-convergent-below-φ fact in its native Nat form, avoiding the
propext-laden Int→Nat casts.  With `a := fib(2n+2)`, `b := fib(2n+1)` (the
consecutive Fibonacci pair that the Pell convergents `pellNum/pellDen` equal),
the Cassini-variant norm `a² + 1 = a·b + b²` holds for all n, and
`PhiAsCut.phiCut_false_of_norm` then reads each convergent as below φ.

All ∅-axiom: Lean-core `Nat.{add_mul, mul_assoc}` pull `propext`, so this uses
the repo's PURE replacements `Meta/Nat/PureNat.{add_mul, mul_assoc, even_sq}` and
`Lib/Math/NatRing.{two_mul_eq, three_mul_eq}`.
-/

namespace E213.Lib.Math.Real213.FibCassiniNat

open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Meta.Nat.PureNat (add_mul mul_assoc even_sq)
open E213.Lib.Math.NatRing (two_mul_eq three_mul_eq)

/-! ## Nat polynomial helpers (all PURE) -/

private theorem tt (x : Nat) : 2 * (2 * x) = 4 * x := (mul_assoc 2 2 x).symm
private theorem twox_x (x : Nat) : 2 * x + x = 3 * x := by
  rw [three_mul_eq, two_mul_eq]
private theorem c4 (x : Nat) : 3 * x + x = 4 * x := by
  rw [show (4 : Nat) = 3 + 1 from rfl, add_mul, Nat.one_mul]
private theorem c5' (x : Nat) : 4 * x + x = 5 * x := by
  rw [show (5 : Nat) = 4 + 1 from rfl, add_mul, Nat.one_mul]
private theorem c5 (x : Nat) : 3 * x + 2 * x = 5 * x := by
  rw [two_mul_eq, ← Nat.add_assoc, c4, c5']
private theorem c2 (x : Nat) : x + x = 2 * x := (two_mul_eq x).symm

private theorem eL (a b : Nat) :
    (2 * a + b) * (2 * a + b) = 4 * (a * a) + (4 * (a * b) + b * b) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, even_sq a, tt (a * a),
      show (2 * a) * b = 2 * (a * b) from mul_assoc 2 a b,
      show b * (2 * a) = 2 * (a * b) from by rw [Nat.mul_comm b (2 * a), mul_assoc],
      Nat.add_assoc (4 * (a * a)) (2 * (a * b)) (2 * (a * b) + b * b),
      ← Nat.add_assoc (2 * (a * b)) (2 * (a * b)) (b * b),
      show 2 * (a * b) + 2 * (a * b) = 4 * (a * b) from by rw [← Nat.two_mul, tt]]

private theorem eM (a b : Nat) :
    (2 * a + b) * (a + b) = 2 * (a * a) + (3 * (a * b) + b * b) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add,
      show (2 * a) * a = 2 * (a * a) from mul_assoc 2 a a,
      show (2 * a) * b = 2 * (a * b) from mul_assoc 2 a b, Nat.mul_comm b a,
      Nat.add_assoc (2 * (a * a)) (2 * (a * b)) (a * b + b * b),
      ← Nat.add_assoc (2 * (a * b)) (a * b) (b * b), twox_x (a * b)]

private theorem eR (a b : Nat) :
    (a + b) * (a + b) = a * a + (2 * (a * b) + b * b) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a,
      Nat.add_assoc (a * a) (a * b) (a * b + b * b),
      ← Nat.add_assoc (a * b) (a * b) (b * b), ← Nat.two_mul (a * b)]

private theorem hR (a b : Nat) :
    (2 * (a * a) + (3 * (a * b) + b * b)) + (a * a + (2 * (a * b) + b * b))
    = (3 * (a * a) + (4 * (a * b) + b * b)) + (a * b + b * b) := by
  rw [show (2 * (a * a) + (3 * (a * b) + b * b)) + (a * a + (2 * (a * b) + b * b))
        = (2 * (a * a) + a * a) + ((3 * (a * b) + 2 * (a * b)) + (b * b + b * b)) from by
        rw [Nat.add_assoc, ← Nat.add_assoc (3 * (a * b) + b * b) (a * a) (2 * (a * b) + b * b),
            Nat.add_comm (3 * (a * b) + b * b) (a * a),
            Nat.add_assoc (a * a) (3 * (a * b) + b * b) (2 * (a * b) + b * b),
            ← Nat.add_assoc (2 * (a * a)) (a * a) _,
            Nat.add_assoc (3 * (a * b)) (b * b) (2 * (a * b) + b * b),
            ← Nat.add_assoc (b * b) (2 * (a * b)) (b * b),
            Nat.add_comm (b * b) (2 * (a * b)),
            Nat.add_assoc (2 * (a * b)) (b * b) (b * b),
            ← Nat.add_assoc (3 * (a * b)) (2 * (a * b)) (b * b + b * b)]]
  rw [twox_x (a * a), c5 (a * b), c2 (b * b)]
  rw [show (3 * (a * a) + (4 * (a * b) + b * b)) + (a * b + b * b)
        = 3 * (a * a) + ((4 * (a * b) + a * b) + (b * b + b * b)) from by
        rw [Nat.add_assoc, ← Nat.add_assoc (4 * (a * b) + b * b) (a * b) (b * b),
            Nat.add_assoc (4 * (a * b)) (b * b) (a * b), Nat.add_comm (b * b) (a * b),
            ← Nat.add_assoc (4 * (a * b)) (a * b) (b * b),
            Nat.add_assoc (4 * (a * b) + a * b) (b * b) (b * b)]]
  rw [c5' (a * b), c2 (b * b)]

/-- The Cassini-variant norm step: from the IH `a² + 1 = a·b + b²` derive the
    same at the doubled pair `(2a+b, a+b)`. -/
private theorem normstep (a b : Nat) (ih : a * a + 1 = a * b + b * b) :
    (2 * a + b) * (2 * a + b) + 1 = (2 * a + b) * (a + b) + (a + b) * (a + b) := by
  rw [eL, eM, eR]
  have hL : 4 * (a * a) + (4 * (a * b) + b * b) + 1
          = (3 * (a * a) + (4 * (a * b) + b * b)) + (a * a + 1) := by
    rw [show (4 : Nat) * (a * a) = 3 * (a * a) + a * a from by
          rw [show (4 : Nat) = 3 + 1 from rfl, add_mul, Nat.one_mul],
        Nat.add_assoc (3 * (a * a)) (a * a) (4 * (a * b) + b * b),
        Nat.add_comm (a * a) (4 * (a * b) + b * b),
        ← Nat.add_assoc (3 * (a * a)) (4 * (a * b) + b * b) (a * a),
        Nat.add_assoc (3 * (a * a) + (4 * (a * b) + b * b)) (a * a) 1]
  rw [hL, hR, ih]

/-! ## Fibonacci couplings (all PURE, from `fib_succ_succ` = rfl) -/

/-- `a := fib(2n+2)` satisfies `a_{n+1} = 2·a_n + b_n`. -/
private theorem aR (n : Nat) :
    fib (2 * n + 4) = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by
  have e1 : fib (2 * n + 4) = fib (2 * n + 3) + fib (2 * n + 2) := rfl
  have e2 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [e1, e2]
  calc fib (2 * n + 2) + fib (2 * n + 1) + fib (2 * n + 2)
      = fib (2 * n + 2) + fib (2 * n + 2) + fib (2 * n + 1) := by
        rw [Nat.add_assoc, Nat.add_comm (fib (2 * n + 1)) (fib (2 * n + 2)),
            ← Nat.add_assoc]
    _ = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by rw [← Nat.two_mul]

/-- `b := fib(2n+1)` satisfies `b_{n+1} = a_n + b_n`. -/
private theorem bR (n : Nat) :
    fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl

/-! ## The Cassini norm ∀ n, and below-φ -/

/-- ★★ **Fibonacci Cassini norm, ∀ n**: `fib(2n+2)² + 1 = fib(2n+2)·fib(2n+1) +
    fib(2n+1)²`.  Induction with `normstep` over the fib couplings `aR`/`bR`.
    All ∅-axiom Nat. -/
theorem fib_cassini_norm (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 2) + 1
    = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have ha : fib (2 * (k + 1) + 2) = 2 * fib (2 * k + 2) + fib (2 * k + 1) := by
      rw [show 2 * (k + 1) + 2 = 2 * k + 4 from by rw [Nat.mul_succ]]; exact aR k
    have hb : fib (2 * (k + 1) + 1) = fib (2 * k + 2) + fib (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by rw [Nat.mul_succ]]; exact bR k
    rw [ha, hb]
    exact normstep (fib (2 * k + 2)) (fib (2 * k + 1)) ih

end E213.Lib.Math.Real213.FibCassiniNat
