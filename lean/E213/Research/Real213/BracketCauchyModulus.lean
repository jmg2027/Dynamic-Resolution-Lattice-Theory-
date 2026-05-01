import E213.Research.Real213.DyadicBracket
import E213.Research.Real213.ConsistentOracle

/-!
# Real213BracketCauchyModulus — quantitative bracket-length halving

Resolves the F6 doc's open status:
"Bracket Cauchy convergence: needs bracket-length halving with
quantitative bound on the modulus N.  Still open but tractable in
the dyadic regime."

## What's now proved

  dyadic_bracket_cauchy_modulus : ∀ L E m k, m ≥ 1 →
    ∀ n ≥ L * k, dyadicCut L (E + n) m k = true.

This says: for any bracket length numerator L, base exponent E,
and target precision (m, k) with m ≥ 1, after at most `L * k`
bisection steps, the bracket length cut at (m, k) is "satisfied"
— i.e., the bracket has shrunk below precision m/k.

## Mathematical content

After n bisection steps, the dyadic bracket has:
  - lenNum unchanged (= L)
  - expE = E + n
  - real length = L / 2^(E + n)

For real length ≤ m/k, we need L * k ≤ m * 2^(E + n).
Taking n ≥ L * k suffices: 2^n ≥ n + 1 ≥ L*k + 1 > L*k.

This gives an explicit, computable, quantitative Cauchy modulus
for the dyadic bracket convergence — closing the open problem.
-/

namespace E213.Research.Real213.BracketCauchyModulus

open E213.Firmware E213.Hypervisor

/-- Lemma: n + 1 ≤ 2^n for all n.  (Tight at n=1: 2 ≤ 2.) -/
private theorem succ_le_two_pow : ∀ n, n + 1 ≤ 2^n
  | 0 => by decide
  | k + 1 => by
    have ih := succ_le_two_pow k
    have h2k : 1 ≤ 2^k := Nat.one_le_two_pow
    calc k + 1 + 1 = (k + 1) + 1 := rfl
      _ ≤ 2^k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2^k + 2^k := Nat.add_le_add_left h2k _
      _ = 2 * 2^k := (Nat.two_mul _).symm
      _ = 2^(k+1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- Lemma: n ≤ 2^n for all n. -/
private theorem le_two_pow (n : Nat) : n ≤ 2^n :=
  Nat.le_trans (Nat.le_succ n) (succ_le_two_pow n)

/-- Lemma: 2^a ≤ 2^b when a ≤ b. -/
private theorem two_pow_mono {a b : Nat} (h : a ≤ b) : 2^a ≤ 2^b :=
  Nat.pow_le_pow_right (by decide : 1 ≤ 2) h

/-- ★★★★★★ Quantitative bracket-length Cauchy modulus.

  For any dyadic bracket with length numerator L, base exponent E,
  and any precision (m, k) with m ≥ 1:

    after `n ≥ L * k` bisection steps, the bracket length cut at
    (m, k) is satisfied (i.e., L / 2^(E + n) ≤ m / k).

  Modulus: N(m, k) = L * k.  Linear in problem size, exponentially
  reliable. -/
theorem dyadic_bracket_cauchy_modulus (L E m k : Nat) (hm : 1 ≤ m) :
    ∀ n, L * k ≤ n → dyadicCut L (E + n) m k = true := by
  intro n hLkn
  show decide (L * k ≤ 2^(E + n) * m) = true
  apply decide_eq_true
  -- m * 2^(E + n) ≥ 1 * 2^n ≥ n + 1 > L*k.
  -- Step 1: 2^(E+n) ≥ 2^n.
  have h_pow_ge : 2^n ≤ 2^(E + n) :=
    two_pow_mono (Nat.le_add_left _ _)
  -- Step 2: 2^n ≥ n + 1.
  have h_succ : n + 1 ≤ 2^n := succ_le_two_pow n
  -- Step 3: 2^(E+n) * m ≥ 2^(E+n) * 1 = 2^(E+n).
  have h_m_pow : 2^(E + n) ≤ 2^(E + n) * m := by
    have : 2^(E + n) * 1 ≤ 2^(E + n) * m :=
      Nat.mul_le_mul_left _ hm
    rwa [Nat.mul_one] at this
  -- Combine: L*k ≤ n ≤ n + 1 ≤ 2^n ≤ 2^(E+n) ≤ 2^(E+n) * m.
  calc L * k ≤ n := hLkn
    _ ≤ n + 1 := Nat.le_succ _
    _ ≤ 2^n := h_succ
    _ ≤ 2^(E + n) := h_pow_ge
    _ ≤ 2^(E + n) * m := h_m_pow

/-! ### Bracket length tends to zero — qualitative form -/

/-- ★★★★★ For any precision (m, k) with m ≥ 1, the bracket length
    eventually fits inside, regardless of starting exponent E.

    Existential form of the Cauchy modulus theorem. -/
theorem dyadic_bracket_eventually_fits (L E m k : Nat) (hm : 1 ≤ m) :
    ∃ N, ∀ n ≥ N, dyadicCut L (E + n) m k = true :=
  ⟨L * k, fun n hn => dyadic_bracket_cauchy_modulus L E m k hm n hn⟩

/-! ### Concrete witnesses -/

/-- bracket length 1, exponent 0, after 5 steps: 1/2^5 = 1/32 ≤ 1/4. -/
theorem bracket_5_steps_le_quarter :
    dyadicCut 1 (0 + 5) 1 4 = true := by decide

/-- bracket length 1, exponent 0, after 10 steps: 1/1024 ≤ 1/100. -/
theorem bracket_10_steps_le_hundredth :
    dyadicCut 1 (0 + 10) 1 100 = true := by decide

/-- Length-3 bracket at exponent 2, after L*k = 3*8 = 24 steps:
    fits inside 1/8 precision. -/
theorem bracket_3_24steps_le_eighth :
    dyadicCut 3 (2 + 24) 1 8 = true := by decide

end E213.Research.Real213.BracketCauchyModulus
