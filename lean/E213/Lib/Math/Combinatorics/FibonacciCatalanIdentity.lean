import E213.Lib.Math.Combinatorics.LucasFibonacci
import E213.Meta.Int213.Order

/-!
# Catalan's identity for Fibonacci numbers (∅-axiom, over `Int`)

Subtraction-free form (`n = a + r`, so `n − r = a`, `n + r = a + 2r`):

  `fib(a+r)² − fib a · fib(a+2r) = (−1)^a · fib(r)²`   (over `Int`).
-/

namespace E213.Lib.Math.Combinatorics.FibonacciCatalanIdentity

open E213.Lib.Math.Combinatorics.FibonacciDivisibility (fib fib_rec fib_add)
open E213.Lib.Math.Combinatorics.LucasFibonacci (fib_rec_cast)
open E213.Meta.Int213.PolyIntM (powInt)

/-! ## d'Ocagne's identity, by induction on `a`. -/

theorem docagne (r a : Nat) :
    (fib (a + 1) : Int) * (fib (a + r) : Int)
        - (fib a : Int) * (fib (a + r + 1) : Int) = powInt (-1) a * (fib r : Int) := by
  induction a with
  | zero =>
    -- goal: fib 1 · fib (0+r) − fib 0 · fib (0+r+1) = (−1)^0 · fib r
    -- Nat index + `rfl`-value rewrites are PURE; finish the Int arithmetic in
    -- term mode with the 213-native (∅-axiom) `zero_mul` / `sub_zero`
    -- (Lean-core `Int.zero_mul` / `Int.sub_zero` are propext-dirty).
    rw [show (0 : Nat) + 1 = 1 from rfl, show (0 : Nat) + r = r from (Nat.zero_add r),
        show (fib 0 : Int) = 0 from rfl, show (fib 1 : Int) = 1 from rfl,
        show powInt (-1 : Int) 0 = 1 from rfl]
    -- goal now: (1:Int) * fib r − (0:Int) * fib (r+1) = (1:Int) * fib r
    exact (congrArg (fun t => (1 : Int) * (fib r : Int) - t)
            (E213.Meta.Int213.zero_mul (fib (r + 1) : Int))).trans
          (E213.Meta.Int213.Order.sub_zero ((1 : Int) * (fib r : Int)))
  | succ k ih =>
    have hi1 : k + 1 + r = (k + r) + 1 := by ring_nat
    have rA : ((fib (k + 1 + 1) : Nat) : Int)
        = (fib k : Int) + (fib (k + 1) : Int) := fib_rec_cast k
    have rB : ((fib ((k + r) + 1 + 1) : Nat) : Int)
        = (fib (k + r) : Int) + (fib ((k + r) + 1) : Int) := fib_rec_cast (k + r)
    have hsign : powInt (-1 : Int) (k + 1) = powInt (-1) k * (-1) := rfl
    -- RHS = -(D k) ; LHS = -(D k) by `ring_intZ`
    have hrhs : powInt (-1 : Int) (k + 1) * (fib r : Int)
        = -((fib (k + 1) : Int) * (fib (k + r) : Int)
              - (fib k : Int) * (fib (k + r + 1) : Int)) := by
      rw [hsign, ih]; ring_intZ
    rw [hi1, rA, rB, hrhs]
    ring_intZ

/-! ## Catalan's identity. -/

/-- ★★★ **Catalan's identity for Fibonacci numbers** (subtraction-free form,
    over `Int`).  With `n = a + r` this reads
    `fib(n)² − fib(n−r)·fib(n+r) = (−1)^(n−r)·fib(r)²`; Cassini is the `r = 1`
    case.

    Route (for `r = s + 1`):
      * `fib(a+r)   = fib(a+1)·fib r + fib a · fib s`   (`fib_add a s`),
      * `fib(a+2r)  = fib(a+r+1)·fib r + fib(a+r)·fib s` (`fib_add (a+r) s`),
    so the Catalan LHS factors as `fib r · D(a)` with `D(a)` the d'Ocagne
    bracket `= (−1)^a · fib r`. -/
theorem fib_catalan_identity (a r : Nat) :
    (fib (a + r) : Int) * (fib (a + r) : Int)
        - (fib a : Int) * (fib (a + 2 * r) : Int)
      = powInt (-1) a * ((fib r : Int) * (fib r : Int)) := by
  cases r with
  | zero =>
    -- r = 0 : fib(a+0)² − fib a · fib(a+2·0) = (−1)^a · fib 0²
    rw [Nat.mul_zero, Nat.add_zero, show (fib 0 : Int) = 0 from rfl]
    -- goal: fib a · fib a − fib a · fib a = powInt (-1) a * (0 * 0)
    have e0 : (fib a : Int) * (fib a : Int) - (fib a : Int) * (fib a : Int) = 0 :=
      E213.Meta.Int213.Order.sub_self_zero _
    rw [e0, E213.Meta.Int213.PolyIntM.mul_zeroZ (0 : Int),
        E213.Meta.Int213.PolyIntM.mul_zeroZ]
  | succ s =>
    -- r = s + 1.  Index normalisations.
    have hIIidx : a + s + 1 = a + (s + 1) := by ring_nat
    -- (II) fib (a + (s+1)) = fib (a+1)·fib (s+1) + fib a · fib s
    have hII : ((fib (a + (s + 1)) : Nat) : Int)
        = (fib (a + 1) : Int) * (fib (s + 1) : Int)
            + (fib a : Int) * (fib s : Int) := by
      have e : fib (a + s + 1) = fib (a + 1) * fib (s + 1) + fib a * fib s := fib_add a s
      rw [← hIIidx, e, Int.ofNat_add, Int.ofNat_mul, Int.ofNat_mul]
    -- (I) fib (a + 2(s+1)) = fib (a+(s+1)+1)·fib (s+1) + fib (a+(s+1))·fib s
    have hI : ((fib (a + 2 * (s + 1)) : Nat) : Int)
        = (fib (a + (s + 1) + 1) : Int) * (fib (s + 1) : Int)
            + (fib (a + (s + 1)) : Int) * (fib s : Int) := by
      have e : fib ((a + (s + 1)) + s + 1)
          = fib ((a + (s + 1)) + 1) * fib (s + 1) + fib (a + (s + 1)) * fib s :=
        fib_add (a + (s + 1)) s
      have hidx : (a + (s + 1)) + s + 1 = a + 2 * (s + 1) := by ring_nat
      rw [hidx] at e
      rw [e, Int.ofNat_add, Int.ofNat_mul, Int.ofNat_mul]
    -- d'Ocagne at r := s+1
    have hD : (fib (a + 1) : Int) * (fib (a + (s + 1)) : Int)
        - (fib a : Int) * (fib (a + (s + 1) + 1) : Int)
          = powInt (-1) a * (fib (s + 1) : Int) := docagne (s + 1) a
    -- the pure ring decomposition (atoms: X = fib(a+(s+1)), Y = fib(a+(s+1)+1),
    -- Q = fib a, P = fib(a+1), R = fib(s+1), S = fib s):
    --   X² − Q·(Y·R + X·S) = R·(P·X − Q·Y) + X·(X − (P·R + Q·S))
    have key :
        (fib (a + (s + 1)) : Int) * (fib (a + (s + 1)) : Int)
          - (fib a : Int)
              * ((fib (a + (s + 1) + 1) : Int) * (fib (s + 1) : Int)
                  + (fib (a + (s + 1)) : Int) * (fib s : Int))
        = (fib (s + 1) : Int)
            * ((fib (a + 1) : Int) * (fib (a + (s + 1)) : Int)
                - (fib a : Int) * (fib (a + (s + 1) + 1) : Int))
          + (fib (a + (s + 1)) : Int)
              * ((fib (a + (s + 1)) : Int)
                  - ((fib (a + 1) : Int) * (fib (s + 1) : Int)
                      + (fib a : Int) * (fib s : Int))) := by
      ring_intZ
    -- assemble
    rw [hI, key, hD, ← hII]
    -- now the second summand is fib(a+(s+1)) · (X − X) = 0
    have hself : (fib (a + (s + 1)) : Int) - (fib (a + (s + 1)) : Int) = 0 :=
      E213.Meta.Int213.Order.sub_self_zero _
    rw [hself, E213.Meta.Int213.PolyIntM.mul_zeroZ, Int.add_zero]
    ring_intZ

/-! ## Smoke checks (small `(a, r)` instances, closed `decide`). -/

theorem catalan_smoke_a3_r2 :
    (fib (3 + 2) : Int) * (fib (3 + 2) : Int)
        - (fib 3 : Int) * (fib (3 + 2 * 2) : Int)
      = powInt (-1) 3 * ((fib 2 : Int) * (fib 2 : Int)) :=
  fib_catalan_identity 3 2

theorem catalan_smoke_a2_r3 :
    (fib (2 + 3) : Int) * (fib (2 + 3) : Int)
        - (fib 2 : Int) * (fib (2 + 2 * 3) : Int)
      = powInt (-1) 2 * ((fib 3 : Int) * (fib 3 : Int)) :=
  fib_catalan_identity 2 3

/-- Cassini as the `r = 1` case of Catalan (subtraction-free, `n = a + 1`):
    `fib(a+1)² − fib a · fib(a+2) = (−1)^a · fib 1² = (−1)^a`. -/
theorem cassini_from_catalan (a : Nat) :
    (fib (a + 1) : Int) * (fib (a + 1) : Int)
        - (fib a : Int) * (fib (a + 2 * 1) : Int)
      = powInt (-1) a * ((fib 1 : Int) * (fib 1 : Int)) :=
  fib_catalan_identity a 1

end E213.Lib.Math.Combinatorics.FibonacciCatalanIdentity
