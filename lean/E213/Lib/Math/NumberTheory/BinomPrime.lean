import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.FactorialLcmDvd
import E213.Meta.Nat.PolyNatMTactic

/-!
# A prime divides its interior binomial coefficients — `q ∣ C(q,t)` for `0<t<q` (∅-axiom)

★★★★★ `prime_dvd_binom` : for a prime `q` and `0 < t < q`,

  `q ∣ binom q t`.

This is the **crux of the Frobenius endomorphism** (the freshman's dream `(a+b)^q ≡ a^q + b^q mod q`):
the binomial theorem's interior terms all vanish mod `q`.  Toward the cubic-reciprocity Frobenius
congruence `g(χ)^q ≡ χ̄(q)·g(χ) (mod q)`.

## Proof

The **absorption identity** `(n+1)·C(n,k) = (k+1)·C(n+1,k+1)` (`succ_mul_binom`, by induction on the
Pascal recursion) gives, at `n+1=q`, `k+1=t`:

  `t · binom q t = q · binom (q−1) (t−1)`,

so `q ∣ t · binom q t`.  Since `q` is prime and `q ∤ t` (because `0 < t < q`), the rational Euclid
lemma `nat_prime_dvd_mul` forces `q ∣ binom q t`.  ∅-axiom throughout (213-native `binom` from
`Simplex/Counts`, no Mathlib).
-/

namespace E213.Lib.Math.NumberTheory.BinomPrime

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Lib.Math.NumberTheory.FactorialLcmDvd (le_of_dvd_pos)

/-- `binom n 0 = 1` — the zeroth column.  By cases on `n` (the Pascal recursion splits on the first
    argument, so `binom n 0` is not `rfl`-reducible with `n` a variable).  ∅-axiom. -/
theorem binom_zero_right : ∀ n : Nat, binom n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

/-- `binom n 1 = n` — the first column of Pascal's triangle.  By induction (`binom (n+1) 1 =
    binom n 0 + binom n 1 = 1 + n`).  ∅-axiom. -/
theorem binom_one : ∀ n : Nat, binom n 1 = n
  | 0 => rfl
  | n + 1 => by
      show binom n 0 + binom n 1 = n + 1
      rw [binom_one n, binom_zero_right n, Nat.add_comm 1 n]

/-- ★★★★ **The absorption identity** — `(n+1)·C(n,k) = (k+1)·C(n+1,k+1)` (the "committee–chair"
    identity).  By induction on `n` with `k` free, using the Pascal recursion of `binom` and the two
    inductive instances at `k` and `k+1`.  ∅-axiom. -/
theorem succ_mul_binom : ∀ n k : Nat, (n + 1) * binom n k = (k + 1) * binom (n + 1) (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by
      rw [show binom 0 (k + 1) = 0 from rfl, show binom (0 + 1) (k + 1 + 1) = 0 from rfl,
          Nat.mul_zero, Nat.mul_zero]
  | n + 1, 0 => by
      show (n + 1 + 1) * binom (n + 1) 0 = 1 * binom (n + 1 + 1) 1
      rw [binom_zero_right (n + 1), binom_one (n + 1 + 1), Nat.mul_one, Nat.one_mul]
  | n + 1, k + 1 => by
      have IH1 := succ_mul_binom n k
      have IH2 := succ_mul_binom n (k + 1)
      have P1 : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl
      have P2 : binom (n + 1 + 1) (k + 1 + 1)
              = binom (n + 1) (k + 1) + binom (n + 1) (k + 1 + 1) := rfl
      have P3 : binom (n + 1) (k + 1 + 1) = binom n (k + 1) + binom n (k + 1 + 1) := rfl
      rw [P1] at IH1
      rw [P3] at IH2
      rw [P2, P1, P3]
      have expand : (n + 1 + 1) * (binom n k + binom n (k + 1))
          = (n + 1) * binom n k + (n + 1) * binom n (k + 1) + (binom n k + binom n (k + 1)) := by
        ring_nat
      rw [expand, IH1, IH2]
      ring_nat

/-- ★★★★★ **A prime divides its interior binomial coefficients** — `q ∣ binom q t` for a prime `q`
    and `0 < t < q`.  From the absorption identity `t·binom q t = q·binom (q−1)(t−1)` (so
    `q ∣ t·binom q t`) and `q ∤ t` (since `0 < t < q`), via the Euclid lemma `nat_prime_dvd_mul`.
    The crux of the Frobenius freshman's dream.  ∅-axiom. -/
theorem prime_dvd_binom (q t : Nat) (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q)
    (ht1 : 1 ≤ t) (htq : t < q) : q ∣ binom q t := by
  rcases q with _ | q'
  · exact absurd hq (by decide)
  · rcases t with _ | t'
    · exact absurd ht1 (by decide)
    · have hid := succ_mul_binom q' t'
      have hdvd : (q' + 1) ∣ (t' + 1) * binom (q' + 1) (t' + 1) := ⟨binom q' t', hid.symm⟩
      have hnpt : ¬ (q' + 1) ∣ (t' + 1) :=
        fun hd => absurd (le_of_dvd_pos (Nat.succ_pos t') hd) (Nat.not_le.mpr htq)
      rcases nat_prime_dvd_mul (q' + 1) hq hqr (t' + 1) (binom (q' + 1) (t' + 1)) hdvd with h | h
      · exact absurd h hnpt
      · exact h

end E213.Lib.Math.NumberTheory.BinomPrime
