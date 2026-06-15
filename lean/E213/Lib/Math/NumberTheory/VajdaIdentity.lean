import E213.Lib.Math.NumberTheory.FibZIdentities

/-!
# Vajda's identity for Fibonacci numbers (over ℤ)

`F(n+i)·F(n+j) − F(n)·F(n+i+j) = (−1)ⁿ · F(i) · F(j)`

built ∅-axiom on the corpus `fibZ` infrastructure (addition formula
`fibZ_add`, shift law `fibZ_shift`, and Cassini ε-form `fibZ_cassini_eps`).
-/

namespace E213.Lib.Math.NumberTheory.VajdaIdentity

open E213.Lib.Math.Analysis.Cauchy.OrbitDimension (fibZ)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign)
open E213.Lib.Math.NumberTheory.FibZIdentities (fibZ_add fibZ_shift fibZ_cassini_eps)

/-- **Vajda's identity** over `ℤ`:
    `F(n+i)·F(n+j) − F(n)·F(n+i+j) = (−1)ⁿ · F(i) · F(j)`.

    Proof: rewrite the three displaced Fibonaccis in the `(F(n), F(n+1))`
    basis via the shift law and the addition formula; the whole expression
    collapses (one `ring_intZ`) to `F(i)·F(j)·(F(n+1)² − F(n)F(n+1) − F(n)²)`,
    and the inner quadratic *is* `(−1)ⁿ` by `fibZ_cassini_eps`. -/
theorem fibZ_vajda (n i j : Nat) :
    fibZ (n + i) * fibZ (n + j) - fibZ n * fibZ (n + i + j)
      = altSign n * fibZ i * fibZ j := by
  have hni : fibZ (n + i)
      = fibZ (n + 1) * fibZ i + fibZ n * (fibZ (i + 1) - fibZ i) := fibZ_shift n i
  have hnj : fibZ (n + j)
      = fibZ (n + 1) * fibZ j + fibZ n * (fibZ (j + 1) - fibZ j) := fibZ_shift n j
  have hnij : fibZ (n + i + j)
      = fibZ (n + i + 1) * fibZ j
        + fibZ (n + i) * (fibZ (j + 1) - fibZ j) := fibZ_shift (n + i) j
  have hni1 : fibZ (n + i + 1)
      = fibZ (n + 1) * fibZ (i + 1) + fibZ n * fibZ i := fibZ_add n i
  have hcas := fibZ_cassini_eps n
  -- The whole LHS collapses to F(i)·F(j)·(F(n+1)² − F(n)F(n+1) − F(n)²).
  have key : fibZ (n + i) * fibZ (n + j) - fibZ n * fibZ (n + i + j)
      = fibZ i * fibZ j
        * (fibZ (n + 1) * fibZ (n + 1) - fibZ n * fibZ (n + 1) - fibZ n * fibZ n) := by
    rw [hnij, hni1, hni, hnj]
    ring_intZ
  rw [key, hcas]
  ring_intZ

/-! ## Corollaries -/

/-- **Cassini's identity** (`i = j = 1`):
    `F(n+1)² − F(n)·F(n+2) = (−1)ⁿ`. -/
theorem fibZ_cassini (n : Nat) :
    fibZ (n + 1) * fibZ (n + 1) - fibZ n * fibZ (n + 2) = altSign n := by
  have h := fibZ_vajda n 1 1
  -- F(n+1)·F(n+1) − F(n)·F(n+1+1) = (−1)ⁿ · F(1) · F(1)
  rw [show fibZ 1 = (1 : Int) from rfl, E213.Meta.Int213.mul_one,
      E213.Meta.Int213.mul_one,
      show n + 1 + 1 = n + 2 from rfl] at h
  exact h

/-- **Catalan's identity** (`i = j = r`):
    `F(n+r)² − F(n)·F(n+2r) = (−1)ⁿ · F(r)²`. -/
theorem fibZ_catalan (n r : Nat) :
    fibZ (n + r) * fibZ (n + r) - fibZ n * fibZ (n + r + r)
      = altSign n * (fibZ r * fibZ r) := by
  have h := fibZ_vajda n r r
  rw [show altSign n * fibZ r * fibZ r = altSign n * (fibZ r * fibZ r) from by ring_intZ] at h
  exact h

/-- **d'Ocagne's identity** (`i = 1`, general `j = m`):
    `F(n+1)·F(n+m) − F(n)·F(n+1+m) = (−1)ⁿ · F(m)`. -/
theorem fibZ_docagne (n m : Nat) :
    fibZ (n + 1) * fibZ (n + m) - fibZ n * fibZ (n + 1 + m)
      = altSign n * fibZ m := by
  have h := fibZ_vajda n 1 m
  rw [show fibZ 1 = (1 : Int) from rfl, E213.Meta.Int213.mul_one] at h
  exact h

/-! ## Concrete smoke tests (closed-form `decide`) -/

-- Cassini at n = 5:  F(6)² − F(5)·F(7) = 8² − 5·13 = 64 − 65 = −1 = (−1)⁵
example : fibZ 6 * fibZ 6 - fibZ 5 * fibZ 7 = altSign 5 := by decide

-- Catalan at n = 4, r = 3:  F(7)² − F(4)·F(10) = 13² − 3·55 = 169 − 165 = 4 = (+1)·F(3)²
example : fibZ 7 * fibZ 7 - fibZ 4 * fibZ 10 = altSign 4 * (fibZ 3 * fibZ 3) := by decide

-- Vajda at n = 3, i = 2, j = 4:
--   F(5)·F(7) − F(3)·F(9) = 5·13 − 2·34 = 65 − 68 = −3 = (−1)³·F(2)·F(4) = −1·1·3
example : fibZ 5 * fibZ 7 - fibZ 3 * fibZ 9 = altSign 3 * fibZ 2 * fibZ 4 := by decide

-- d'Ocagne at n = 4, m = 6:
--   F(5)·F(10) − F(4)·F(11) = 5·55 − 3·89 = 275 − 267 = 8 = (+1)·F(6)
example : fibZ 5 * fibZ 10 - fibZ 4 * fibZ 11 = altSign 4 * fibZ 6 := by decide

end E213.Lib.Math.NumberTheory.VajdaIdentity
