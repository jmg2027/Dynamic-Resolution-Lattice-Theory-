import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
import E213.Lib.Math.NumberTheory.BinomPrime
import E213.Meta.Nat.BinomSymm

/-!
# The binomial theorem in `ℤ[ω]` — `(a+b)^n = Σ_k C(n,k)·a^k·b^{n−k}` (∅-axiom)

★★★★★ `add_pow` : in the commutative ring `ℤ[ω]`,

  `(a + b)^n = Σ_{k=0}^{n} binom n k · a^k · b^{n−k}`   (`sumRange` over `[0, n+1)`).

The binomial theorem rebuilt over the Eisenstein integers, with the binomial coefficient embedded
as `cz n k = ofInt (binom n k)` (the 213-native Pascal `binom` from `Simplex/Counts`).  The proof is
the classical Pascal induction: `(a+b)^{n+1} = (a+b)^n·(a+b)`, distribute, shift one sum down by one
index (`sumRange_succ_bottom`), and recombine via Pascal's rule `binom (n+1)(k+1) = binom n k +
binom n (k+1)` (`cz_pascal`), the boundary terms supplying `a^{n+1}` and `b^{n+1}`.

Toward the **freshman's dream** `(a+b)^q ≡ a^q + b^q (mod q)` (prime `q`): all interior coefficients
`binom q k` (`0<k<q`) are divisible by `q` (`BinomPrime.prime_dvd_binom`), so only the endpoints
survive mod `q` — the Frobenius endomorphism for the cubic-reciprocity congruence.

PURE (∅-axiom).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinBinomial

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
  (pow pow_zero pow_succ one one_mul mul_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sumRange_zero sumRange_succ sum_add sum_mul_right sum_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (ofInt_add)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.NumberTheory.BinomPrime (binom_zero_right)
open E213.Meta.Nat.BinomSymm (binom_diag)
open E213.Meta.Algebra213.Ring213
  (add_assoc add_comm add_zero zero_add mul_add add_mul mul_assoc)
open E213.Meta.Algebra213.CommRing213 (mul_comm)
open E213.Tactic.NatHelper (sub_add_cancel sub_pos_of_lt)

/-- **Pure `n − m − k = n − (m + k)`** — the 213-native replacement for the `propext`-dirty
    `Nat.sub_sub` (Lean-core well-founded recursion).  Induction on `k` via `Nat.sub_succ`. -/
theorem sub_sub (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.sub_succ, ih, Nat.add_succ, Nat.sub_succ]

/-- The binomial coefficient embedded in `ℤ[ω]`: `cz n k = ofInt (binom n k)`. -/
def cz (n k : Nat) : ZOmega := ofInt ((binom n k : Nat) : Int)

/-- `cz n 0 = 1`. -/
theorem cz_zero (n : Nat) : cz n 0 = one := by
  show ofInt ((binom n 0 : Nat) : Int) = one
  rw [binom_zero_right n]; rfl

/-- `cz n n = 1`. -/
theorem cz_diag (n : Nat) : cz n n = one := by
  show ofInt ((binom n n : Nat) : Int) = one
  rw [binom_diag n]; rfl

/-- **Pascal's rule in `ℤ[ω]`** — `cz (n+1) (k+1) = cz n k + cz n (k+1)`. -/
theorem cz_pascal (n k : Nat) : cz (n + 1) (k + 1) = cz n k + cz n (k + 1) := by
  show ofInt ((binom (n + 1) (k + 1) : Nat) : Int)
     = ofInt ((binom n k : Nat) : Int) + ofInt ((binom n (k + 1) : Nat) : Int)
  rw [show binom (n + 1) (k + 1) = binom n k + binom n (k + 1) from rfl,
      show ((binom n k + binom n (k + 1) : Nat) : Int)
         = ((binom n k : Nat) : Int) + ((binom n (k + 1) : Nat) : Int) from rfl, ← ofInt_add]

/-- The binomial term `binom n k · a^k · b^{n−k}` in `ℤ[ω]`. -/
def bterm (a b : ZOmega) (n k : Nat) : ZOmega := cz n k * (pow a k * pow b (n - k))

/-- **Multiply a binomial term by `a`** — raises the `a`-exponent: `bterm a b n k · a =
    cz n k · (a^{k+1}·b^{n−k})`. -/
theorem bterm_mul_a (a b : ZOmega) (n k : Nat) :
    bterm a b n k * a = cz n k * (pow a (k + 1) * pow b (n - k)) := by
  show cz n k * (pow a k * pow b (n - k)) * a = cz n k * (pow a (k + 1) * pow b (n - k))
  have inner : pow a k * pow b (n - k) * a = pow a (k + 1) * pow b (n - k) := by
    rw [mul_assoc, mul_comm (pow b (n - k)) a, ← mul_assoc, ← pow_succ]
  rw [mul_assoc, inner]

/-- **Multiply a binomial term by `b`** — raises the `b`-exponent: `bterm a b n k · b =
    cz n k · (a^k·b^{(n−k)+1})`. -/
theorem bterm_mul_b (a b : ZOmega) (n k : Nat) :
    bterm a b n k * b = cz n k * (pow a k * pow b ((n - k) + 1)) := by
  show cz n k * (pow a k * pow b (n - k)) * b = cz n k * (pow a k * pow b ((n - k) + 1))
  have inner : pow a k * pow b (n - k) * b = pow a k * pow b ((n - k) + 1) := by
    rw [mul_assoc, ← pow_succ]
  rw [mul_assoc, inner]

/-- **Peel the bottom term of a `sumRange`** — `Σ_{k<n+1} f k = f 0 + Σ_{k<n} f (k+1)`.  Reindexing
    from below, the dual of `sumRange_succ`.  By induction on `n`. -/
theorem sumRange_succ_bottom (f : Nat → ZOmega) : ∀ n : Nat,
    sumRange f (n + 1) = f 0 + sumRange (fun k => f (k + 1)) n
  | 0 => by
      show (0 : ZOmega) + f 0 = f 0 + 0
      rw [zero_add, add_zero]
  | n + 1 => by
      show sumRange f (n + 1) + f (n + 1) = f 0 + (sumRange (fun k => f (k + 1)) n + f (n + 1))
      rw [sumRange_succ_bottom f n, add_assoc]

/-- ★★★★★ **The binomial theorem in `ℤ[ω]`** — `(a+b)^n = Σ_{k=0}^{n} binom n k · a^k · b^{n−k}`.
    Classical Pascal induction: distribute `(a+b)^{n+1} = (a+b)^n·(a+b)`, shift the `a`-sum down one
    index, recombine via `cz_pascal`.  ∅-axiom (PURE). -/
theorem add_pow (a b : ZOmega) : ∀ n : Nat,
    pow (a + b) n = sumRange (fun k => bterm a b n k) (n + 1)
  | 0 => by
      show one = sumRange (fun k => bterm a b 0 k) 1
      show one = (0 : ZOmega) + bterm a b 0 0
      rw [zero_add]
      show one = cz 0 0 * (pow a 0 * pow b 0)
      rw [cz_diag, pow_zero, pow_zero, one_mul, one_mul]
  | n + 1 => by
      -- (a+b)^{n+1} = (a+b)^n · (a+b)  =  S·a + S·b   where S = Σ_{k<n+1} bterm n k
      show pow (a + b) n * (a + b) = sumRange (fun k => bterm a b (n + 1) k) (n + 1 + 1)
      rw [add_pow a b n, mul_add,
          ← sum_mul_right a (fun k => bterm a b n k) (n + 1),
          ← sum_mul_right b (fun k => bterm a b n k) (n + 1),
          sum_congr (n + 1) (fun k _ => bterm_mul_a a b n k),
          sum_congr (n + 1) (fun k _ => bterm_mul_b a b n k),
          sumRange_succ (fun k => cz n k * (pow a (k + 1) * pow b (n - k))) n,
          sumRange_succ_bottom (fun k => cz n k * (pow a k * pow b ((n - k) + 1))) n]
      -- LHS = (SA + a^{n+1}) + (b^{n+1} + SB)
      rw [show cz n n * (pow a (n + 1) * pow b (n - n)) = pow a (n + 1) by
            rw [Nat.sub_self, cz_diag, pow_zero, mul_one, one_mul],
          show cz n 0 * (pow a 0 * pow b ((n - 0) + 1)) = pow b (n + 1) by
            rw [Nat.sub_zero, cz_zero, pow_zero, one_mul, one_mul]]
      -- RHS target: peel (k=n+1 → a^{n+1}) and (k=0 → b^{n+1})
      rw [sumRange_succ (fun k => bterm a b (n + 1) k) (n + 1),
          sumRange_succ_bottom (fun k => bterm a b (n + 1) k) n,
          show bterm a b (n + 1) (n + 1) = pow a (n + 1) by
            show cz (n + 1) (n + 1) * (pow a (n + 1) * pow b ((n + 1) - (n + 1))) = pow a (n + 1)
            rw [Nat.sub_self, cz_diag, pow_zero, mul_one, one_mul],
          show bterm a b (n + 1) 0 = pow b (n + 1) by
            show cz (n + 1) 0 * (pow a 0 * pow b ((n + 1) - 0)) = pow b (n + 1)
            rw [Nat.sub_zero, cz_zero, pow_zero, one_mul, one_mul]]
      -- merge the two interior sums to the target interior
      have hmerge :
          sumRange (fun k => cz n k * (pow a (k + 1) * pow b (n - k))) n
            + sumRange (fun k => cz n (k + 1) * (pow a (k + 1) * pow b ((n - (k + 1)) + 1))) n
          = sumRange (fun k => bterm a b (n + 1) (k + 1)) n := by
        rw [← sum_add (fun k => cz n k * (pow a (k + 1) * pow b (n - k)))
                      (fun k => cz n (k + 1) * (pow a (k + 1) * pow b ((n - (k + 1)) + 1))) n]
        exact sum_congr n (fun k hk => by
          have hbexp : (n - (k + 1)) + 1 = n - k := by
            rw [← sub_sub, sub_add_cancel (sub_pos_of_lt hk)]
          show cz n k * (pow a (k + 1) * pow b (n - k))
             + cz n (k + 1) * (pow a (k + 1) * pow b ((n - (k + 1)) + 1))
             = cz (n + 1) (k + 1) * (pow a (k + 1) * pow b ((n + 1) - (k + 1)))
          rw [hbexp, Nat.succ_sub_succ, ← add_mul, ← cz_pascal n k])
      -- now: (SA + pa) + (pb + SB) = (pb + (SA+SB)) + pa  with SA+SB = target interior
      rw [← hmerge]
      generalize sumRange (fun k => cz n k * (pow a (k + 1) * pow b (n - k))) n = sA
      generalize sumRange (fun k => cz n (k + 1) * (pow a (k + 1) * pow b ((n - (k + 1)) + 1))) n = sB
      generalize pow a (n + 1) = pa
      generalize pow b (n + 1) = pb
      rw [add_assoc sA pa (pb + sB), add_comm pa (pb + sB), ← add_assoc sA (pb + sB) pa,
          ← add_assoc sA pb sB, add_comm sA pb, add_assoc pb sA sB]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinBinomial
