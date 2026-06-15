import E213.Lib.Math.NumberTheory.FibZIdentities
import E213.Lib.Math.NumberTheory.MobiusFunction
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Nat.PolyNatMTactic

/-!
# Classical Fibonacci partial-sum identities over ℤ (∅-axiom)

The four famous Fibonacci summation identities, stated on the **corpus integer
Fibonacci** `fibZ : Nat → Int` (`Analysis/Cauchy/OrbitDimension`,
`fibZ 0 = 0`, `fibZ 1 = 1`, `fibZ (n+2) = fibZ (n+1) + fibZ n`) and the corpus
Int range-sum `sumZ n f = Σ_{j<n} f j` (`NumberTheory/MobiusFunction`).

  * `fibZ_sum`       `Σ_{k=0}^{n} F_k = F_{n+2} − 1`          (`sumZ (n+1) fibZ`)
  * `fibZ_sq_sum`    `Σ_{k=0}^{n} F_k² = F_n · F_{n+1}`       (`sumZ (n+1) …`)
  * `fibZ_even_sum`  `Σ_{k=0}^{n} F_{2k} = F_{2n+1} − 1`      (`sumZ (n+1) …`)
  * `fibZ_odd_sum`   `Σ_{k<n} F_{2k+1} = F_{2n}`              (`sumZ n …`)

Each is a one-variable `Nat.rec` induction on the recurrence
`fibZ (n+2) = fibZ (n+1) + fibZ n` (`fibZ_rec`), closed with `ring_intZ`.
All ∅-axiom.

These are genuinely absent over `fibZ`: the corpus carries Cassini / Vajda /
Catalan / d'Ocagne (`VajdaIdentity`), gcd / divisibility, and the `Nat`-`fib`
sum identities (`Combinatorics/FibonacciSums`), but no `fibZ`/`sumZ` partial-sum
identity existed.
-/

namespace E213.Lib.Math.NumberTheory.FibZSums

open E213.Lib.Math.Analysis.Cauchy.OrbitDimension (fibZ)
open E213.Lib.Math.NumberTheory.FibZIdentities (fibZ_rec)
open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ)

/-- `sumZ` successor step (holds by `rfl`): `Σ_{j<n+1} f = (Σ_{j<n} f) + f n`. -/
theorem sumZ_succ (n : Nat) (f : Nat → Int) : sumZ (n + 1) f = sumZ n f + f n := rfl

/-! ## ★★★ Partial sum `Σ_{k=0}^{n} F_k = F_{n+2} − 1` -/

/-- **Fibonacci partial-sum identity** over `ℤ`:
    `Σ_{k=0}^{n} F_k = F_{n+2} − 1`.  Convention: `sumZ (n+1) fibZ` is the
    inclusive sum `F_0 + … + F_n`.  Step uses `F_{k+3} = F_{k+2} + F_{k+1}`. -/
theorem fibZ_sum (n : Nat) :
    sumZ (n + 1) fibZ = fibZ (n + 2) - 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [sumZ_succ, ih]
    show fibZ (k + 2) - 1 + fibZ (k + 1) = fibZ (k + 1 + 2) - 1
    rw [show k + 1 + 2 = (k + 1) + 2 from rfl, fibZ_rec (k + 1),
        show (k + 1) + 1 = k + 2 from rfl]
    ring_intZ

/-! ## ★★★ Sum of squares `Σ_{k=0}^{n} F_k² = F_n · F_{n+1}` -/

/-- **Fibonacci sum-of-squares identity** over `ℤ`:
    `Σ_{k=0}^{n} F_k² = F_n · F_{n+1}` ("Fibonacci rectangle").
    Step: `F_n F_{n+1} + F_{n+1}² = F_{n+1}(F_n + F_{n+1}) = F_{n+1} F_{n+2}`. -/
theorem fibZ_sq_sum (n : Nat) :
    sumZ (n + 1) (fun k => fibZ k * fibZ k) = fibZ n * fibZ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [sumZ_succ, ih]
    show fibZ k * fibZ (k + 1) + fibZ (k + 1) * fibZ (k + 1)
        = fibZ (k + 1) * fibZ (k + 1 + 1)
    rw [show k + 1 + 1 = k + 2 from rfl, fibZ_rec k]
    ring_intZ

/-! ## ★★ Even-indexed sum `Σ_{k=0}^{n} F_{2k} = F_{2n+1} − 1` -/

/-- **Even-indexed Fibonacci partial sum** over `ℤ`:
    `Σ_{k=0}^{n} F_{2k} = F_{2n+1} − 1`.  (Since `F_0 = 0`, this equals the
    classical `Σ_{k=1}^{n} F_{2k} = F_{2n+1} − 1`.)
    Step: `(F_{2k+1} − 1) + F_{2k+2} = F_{2k+3} − 1`. -/
theorem fibZ_even_sum (n : Nat) :
    sumZ (n + 1) (fun k => fibZ (2 * k)) = fibZ (2 * n + 1) - 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [sumZ_succ, ih]
    show fibZ (2 * k + 1) - 1 + fibZ (2 * (k + 1)) = fibZ (2 * (k + 1) + 1) - 1
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring_nat,
        show (2 * k + 1) + 1 + 1 = (2 * k + 1) + 2 from rfl,
        fibZ_rec (2 * k + 1)]
    ring_intZ

/-! ## ★★ Odd-indexed sum `Σ_{k<n} F_{2k+1} = F_{2n}` -/

/-- **Odd-indexed Fibonacci partial sum** over `ℤ`:
    `Σ_{k=0}^{n-1} F_{2k+1} = F_{2n}` (stated `sumZ n …`, subtraction-free in the
    index).  Step: `F_{2k} + F_{2k+1} = F_{2k+2}`. -/
theorem fibZ_odd_sum (n : Nat) :
    sumZ n (fun k => fibZ (2 * k + 1)) = fibZ (2 * n) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [sumZ_succ, ih]
    show fibZ (2 * k) + fibZ (2 * k + 1) = fibZ (2 * (k + 1))
    rw [show 2 * (k + 1) = (2 * k) + 2 from by ring_nat, fibZ_rec (2 * k),
        show (2 * k) + 1 = 2 * k + 1 from rfl]
    ring_intZ

/-! ## Concrete smoke tests (closed-form `decide`) -/

-- Σ_{k=0}^{5} F_k = 0+1+1+2+3+5 = 12 = F_7 − 1 = 13 − 1
example : sumZ 6 fibZ = fibZ 7 - 1 := by decide
-- Σ_{k=0}^{5} F_k² = 0+1+1+4+9+25 = 40 = F_5·F_6 = 5·8
example : sumZ 6 (fun k => fibZ k * fibZ k) = fibZ 5 * fibZ 6 := by decide
-- Σ_{k=0}^{4} F_{2k} = 0+1+3+8+21 = 33 = F_9 − 1 = 34 − 1
example : sumZ 5 (fun k => fibZ (2 * k)) = fibZ 9 - 1 := by decide
-- Σ_{k=0}^{3} F_{2k+1} = 1+2+5+13 = 21 = F_8
example : sumZ 4 (fun k => fibZ (2 * k + 1)) = fibZ 8 := by decide

end E213.Lib.Math.NumberTheory.FibZSums
