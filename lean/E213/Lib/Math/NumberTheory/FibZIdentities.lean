import E213.Lib.Math.Analysis.Cauchy.OrbitDimension
import E213.Lib.Math.Algebra.Linalg213.FibCassiniDet

/-!
# Integer Fibonacci identities — toward the 5-adic LTE law

Algebraic identities for `fibZ : Nat → Int` (the C-finite orbit-dimension-2
witness, `Analysis/Cauchy/OrbitDimension`), built ∅-axiom over `ring_intZ`,
on the path to `ν₅(F_n) = ν₅(n)` (`FibZValuation.fibN_val_law`).

The chain is:

  1. **Addition formula** `F_{m+n+1} = F_{m+1}F_{n+1} + F_m F_n` (here).
  2. Doubling / index-multiplication recurrence `F_{(k+1)m} = L_m F_{km}
     − (−1)ᵐ F_{(k−1)m}`.
  3. Quintupling `F_{5m} = F_m·(25F_m⁴ + 25(−1)ᵐ F_m² + 5)`.
  4. `ν₅` of the bracket `= 1` ⟹ `ν₅(F_{5m}) = ν₅(F_m) + 1` (Euclid for 5).
  5. Strong induction ⟹ `ν₅(F_n) = ν₅(n)`.
-/

namespace E213.Lib.Math.NumberTheory.FibZIdentities

open E213.Lib.Math.Analysis.Cauchy.OrbitDimension (fibZ)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign)
open E213.Lib.Math.Algebra.Linalg213.FibCassiniDet (cassini_fibZ_eq_altSign)

/-- The defining recurrence, named (holds by `rfl`). -/
theorem fibZ_rec (n : Nat) : fibZ (n + 2) = fibZ (n + 1) + fibZ n := rfl

/-! ## The addition formula

`F_{m+n+1} = F_{m+1}·F_{n+1} + F_m·F_n`, by two-step induction on `n`
(carrying the pair `(P n, P (n+1))`). -/

private theorem fibZ_add_pair (m : Nat) : ∀ n,
    (fibZ (m + n + 1) = fibZ (m + 1) * fibZ (n + 1) + fibZ m * fibZ n)
    ∧ (fibZ (m + n + 2) = fibZ (m + 1) * fibZ (n + 2) + fibZ m * fibZ (n + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show fibZ (m + 1) = fibZ (m + 1) * fibZ 1 + fibZ m * fibZ 0
      rw [show fibZ 1 = (1 : Int) from rfl, show fibZ 0 = (0 : Int) from rfl,
          E213.Meta.Int213.mul_one, Int.mul_zero, Int.add_zero]
    · show fibZ (m + 2) = fibZ (m + 1) * fibZ 2 + fibZ m * fibZ 1
      rw [fibZ_rec m, show fibZ 2 = (1 : Int) from rfl,
          show fibZ 1 = (1 : Int) from rfl, E213.Meta.Int213.mul_one, E213.Meta.Int213.mul_one]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show fibZ (m + k + 3) = fibZ (m + 1) * fibZ (k + 3) + fibZ m * fibZ (k + 2)
    rw [show fibZ (m + k + 3) = fibZ (m + k + 2) + fibZ (m + k + 1) from rfl,
        h1, h2,
        show fibZ (k + 3) = fibZ (k + 2) + fibZ (k + 1) from rfl,
        show fibZ (k + 2) = fibZ (k + 1) + fibZ k from rfl]
    ring_intZ

/-- **Fibonacci addition formula** over `ℤ`: `F_{m+n+1} = F_{m+1}F_{n+1}
    + F_m F_n`.  The multiplicative backbone of every index-composition
    identity (doubling, quintupling, strong divisibility). -/
theorem fibZ_add (m n : Nat) :
    fibZ (m + n + 1) = fibZ (m + 1) * fibZ (n + 1) + fibZ m * fibZ n :=
  (fibZ_add_pair m n).1

/-! ## The shift / composition law

`F_{j+m} = F_{j+1}·F_m + F_j·(F_{m+1} − F_m)` — the "add `m` to the index"
map, from two addition-formula instances and the backward recurrence. -/

theorem fibZ_shift (j m : Nat) :
    fibZ (j + m) = fibZ (j + 1) * fibZ m + fibZ j * (fibZ (m + 1) - fibZ m) := by
  have hA := fibZ_add j m       -- F_{j+m+1} = F_{j+1}F_{m+1} + F_j F_m
  have hB := fibZ_add j (m + 1) -- F_{j+m+2} = F_{j+1}F_{m+2} + F_j F_{m+1}
  have hbk : fibZ (j + m) = fibZ (j + m + 2) - fibZ (j + m + 1) := by
    rw [fibZ_rec (j + m)]; ring_intZ
  rw [hbk, hA, show fibZ (j + m + 2) = fibZ (j + (m + 1) + 1) from rfl, hB,
      show fibZ (m + 2) = fibZ (m + 1) + fibZ m from rfl]
  ring_intZ

/-! ## Lucas numbers and the `L² = 5F² ∓ 4` identity -/

/-- `L_m = 2F_{m+1} − F_m` (`= F_{m+1} + F_{m−1}`), all `m`. -/
def lucasZ (m : Nat) : Int := 2 * fibZ (m + 1) - fibZ m

/-- `(−1)²ⁿ = 1`: the alternating sign squares to one. -/
theorem altSign_sq (m : Nat) : altSign m * altSign m = 1 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    show -(altSign k) * -(altSign k) = 1
    have h : -(altSign k) * -(altSign k) = altSign k * altSign k := by ring_intZ
    rw [h]; exact ih

/-- Cassini, rearranged for the `m`-pair: `F_{m+1}² − F_m F_{m+1} − F_m²
    = −(−1)^{m+1} = (−1)ᵐ = altSign m`.  The structural `ε = (−1)ᵐ`. -/
theorem fibZ_cassini_eps (m : Nat) :
    fibZ (m + 1) * fibZ (m + 1) - fibZ m * fibZ (m + 1) - fibZ m * fibZ m
      = altSign m := by
  have hc := cassini_fibZ_eq_altSign m  -- F_m F_{m+2} − F_{m+1}² = altSign (m+1)
  rw [show fibZ (m + 2) = fibZ (m + 1) + fibZ m from rfl,
      show altSign (m + 1) = -(altSign m) from rfl] at hc
  -- hc : F_m (F_{m+1}+F_m) − F_{m+1}² = −altSign m
  have hrw : fibZ (m + 1) * fibZ (m + 1) - fibZ m * fibZ (m + 1) - fibZ m * fibZ m
      = -(fibZ m * (fibZ (m + 1) + fibZ m) - fibZ (m + 1) * fibZ (m + 1)) := by ring_intZ
  rw [hrw, hc, Int.neg_neg]

/-- **Doubling**: `F_{2m} = F_m · L_m`. -/
theorem fibZ_two_mul (m : Nat) : fibZ (m + m) = fibZ m * lucasZ m := by
  have hs := fibZ_shift m m
  rw [hs]; show _ = fibZ m * (2 * fibZ (m + 1) - fibZ m); ring_intZ

/-- **Doubling (odd)**: `F_{2m+1} = F_{m+1}² + F_m²`. -/
theorem fibZ_two_mul_succ (m : Nat) :
    fibZ (m + m + 1) = fibZ (m + 1) * fibZ (m + 1) + fibZ m * fibZ m :=
  fibZ_add m m

/-- **`L² = 5F² + 4·(−1)ᵐ`** (i.e. `L_m² − 5F_m² = ∓4`).  The
    Lucas–Fibonacci companion of the Cassini unit. -/
theorem lucasZ_sq (m : Nat) :
    lucasZ m * lucasZ m = 5 * (fibZ m * fibZ m) + 4 * altSign m := by
  have he := fibZ_cassini_eps m
  show (2 * fibZ (m + 1) - fibZ m) * (2 * fibZ (m + 1) - fibZ m)
        = 5 * (fibZ m * fibZ m) + 4 * altSign m
  rw [← he]; ring_intZ

/-! ## The index-multiplication recurrence

`F_{b+2m} = L_m·F_{b+m} − (−1)ᵐ·F_b` — the second-order recurrence in the
index multiplier.  Once `(−1)ᵐ` is replaced by its Cassini value it is a
pure polynomial identity (`ring_intZ`).  Iterating it `b = 0..3m` lifts
`F_m` to `F_{2m}, …, F_{5m}`. -/

theorem fibZ_index_rec (b m : Nat) :
    fibZ (b + m + m) = lucasZ m * fibZ (b + m) - altSign m * fibZ b := by
  have hbm  : fibZ (b + m) =
      fibZ (b + 1) * fibZ m + fibZ b * (fibZ (m + 1) - fibZ m) := fibZ_shift b m
  have hbmm : fibZ (b + m + m) =
      fibZ (b + m + 1) * fibZ m
        + fibZ (b + m) * (fibZ (m + 1) - fibZ m) := fibZ_shift (b + m) m
  have hbm1 : fibZ (b + m + 1) =
      fibZ (b + 1) * fibZ (m + 1) + fibZ b * fibZ m := fibZ_add b m
  have he := fibZ_cassini_eps m
  rw [hbmm, hbm1, hbm, show lucasZ m = 2 * fibZ (m + 1) - fibZ m from rfl,
      ← he]
  ring_intZ

/-! ## The quintupling identity

`F_{5m} = F_m · (25 F_m⁴ + 25(−1)ᵐ F_m² + 5)`.  Iterating the
index-multiplication recurrence to `k = 4` gives `F_{5m} = (L⁴ − 3εL² +
ε²)·F_m`; then `ε² = 1` and `L² = 5F² + 4ε` collapse the bracket. -/

/-- Pure algebra core: with `L² = 5x² + 4e` already substituted and
    `e² = 1`, the quintupling bracket equals `25x⁴ + 25e·x² + 5`. -/
private theorem quint_algebra (x e : Int) (he : e * e = 1) :
    (5 * (x * x) + 4 * e) * (5 * (x * x) + 4 * e) * x
        - 3 * e * (5 * (x * x) + 4 * e) * x + (e * e) * x
      = x * (25 * (x * x * x * x) + 25 * e * (x * x) + 5) := by
  have hcorr :
      (5 * (x * x) + 4 * e) * (5 * (x * x) + 4 * e) * x
          - 3 * e * (5 * (x * x) + 4 * e) * x + (e * e) * x
        = x * (25 * (x * x * x * x) + 25 * e * (x * x) + 5)
          + 5 * x * (e * e - 1) := by ring_intZ
  rw [hcorr, he, show (1 : Int) - 1 = 0 from by decide, Int.mul_zero, Int.add_zero]

/-- **Quintupling identity** over `ℤ`: `F_{5m} = F_m·(25F_m⁴ + 25(−1)ᵐF_m²
    + 5)`.  The bracket `= 5·(5F_m⁴ + 5(−1)ᵐF_m² + 1)` has inner factor
    `≡ 1 (mod 5)`, so `ν₅(F_{5m}) = ν₅(F_m) + 1` — the lifting-the-exponent
    engine for `ν₅(F_n) = ν₅(n)`. -/
theorem fibZ_quintuple (m : Nat) :
    fibZ (m + m + m + m + m)
      = fibZ m * (25 * (fibZ m * fibZ m * fibZ m * fibZ m)
                  + 25 * altSign m * (fibZ m * fibZ m) + 5) := by
  have key : fibZ (m + m + m + m + m)
      = lucasZ m * lucasZ m * (lucasZ m * lucasZ m) * fibZ m
        - 3 * altSign m * (lucasZ m * lucasZ m) * fibZ m
        + altSign m * altSign m * fibZ m := by
    rw [fibZ_index_rec (m + m + m) m, fibZ_index_rec (m + m) m,
        fibZ_index_rec m m, fibZ_two_mul m]
    ring_intZ
  rw [key, lucasZ_sq m]
  exact quint_algebra (fibZ m) (altSign m) (altSign_sq m)

/-- **Factored quintupling**: `F_{5m} = 5·(C_m · F_m)` with cofactor
    `C_m = 5F_m⁴ + 5(−1)ᵐF_m² + 1`.  Exposes the single guaranteed factor
    of `5` — the lower half `ν₅(F_{5m}) ≥ ν₅(F_m) + 1` of the lift.  (The
    matching upper half needs `5 ∤ C_m`, true since `C_m = 5·(F_m⁴ +
    (−1)ᵐF_m²) + 1 ≡ 1 mod 5`; then Euclid for the prime `5` gives
    equality — the remaining valuation-bookkeeping rung.) -/
theorem fibZ_quintuple_factored (m : Nat) :
    fibZ (m + m + m + m + m)
      = 5 * ((5 * (fibZ m * fibZ m * fibZ m * fibZ m)
              + 5 * altSign m * (fibZ m * fibZ m) + 1) * fibZ m) := by
  rw [fibZ_quintuple m]; ring_intZ

/-- `5 ∣ F_{5m}` for every `m` — the index-`5` instance of the rank of
    apparition, read on `ℤ`. -/
theorem five_dvd_fibZ_quintuple (m : Nat) :
    (5 : Int) ∣ fibZ (m + m + m + m + m) :=
  ⟨_, fibZ_quintuple_factored m⟩

end E213.Lib.Math.NumberTheory.FibZIdentities
