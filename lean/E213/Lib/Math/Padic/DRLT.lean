import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Norm
/-!
# Real213-p-adic — DRLT integration

The DRLT resolution lattice uses `N_U = 5^25` as its count-Lens
universe size at fractal level 2.  The 5-adic Real213 picks up
exactly where the finite-resolution lattice stops, providing a
canonical embedding `ℕ ↪ ZpSeq 5` for any natural number.

The lift `N_U → ZpSeq 5` is `digits_of_nat 5 N_U`, which has
digit 25 equal to `1` and all other digits equal to `0` (since
`5^25 = 1 · 5^25 + 0 · …`).

Whether the "infinite" 5-adic structure beyond the resolution
limit is operationally meaningful in DRLT, or is a formal
extension only, is itself a research question — see
`seed/RESOLUTION_LIMIT_SPEC.md`.
-/

namespace E213.Lib.Math.Padic

/-- The canonical 5-adic lift of `N_U = 5^25`. -/
def canonical_5adic_NU : ZpSeq 5 :=
  ZpSeq.digits_of_nat 5 (by decide) (5^25)

/-- The all-zero 5-adic. -/
def canonical_5adic_zero : ZpSeq 5 :=
  ZpSeq.zero 5 (by decide)

/-- Smoke: digit-0 of `5^25` in base 5 is `0` (since `5^25` is
    divisible by `5`). -/
theorem canonical_5adic_NU_digit_0 :
    (canonical_5adic_NU.digits 0).val = 0 := rfl

/-- Smoke: digit-1 of `5^25` in base 5 is `0`. -/
theorem canonical_5adic_NU_digit_1 :
    (canonical_5adic_NU.digits 1).val = 0 := rfl

/-- PURE `n / n = 1` for `0 < n`. -/
private theorem nat_div_self (n : Nat) (hn : 0 < n) : n / n = 1 := by
  rw [Nat.div_eq, if_pos ⟨hn, Nat.le_refl n⟩, Nat.sub_self, Nat.zero_div]

/-- Digit-25 of `5^25` in base 5 is `1` — the leading digit
    in the canonical representation `5^25 = 1·5^25`. -/
theorem canonical_5adic_NU_digit_25 :
    (canonical_5adic_NU.digits 25).val = 1 := by
  show ((5 : Nat)^25 / 5^25) % 5 = 1
  rw [nat_div_self (5^25) (by decide)]

/-- Digit-26 of `5^25` in base 5 is `0` — beyond the leading digit. -/
theorem canonical_5adic_NU_digit_26 :
    (canonical_5adic_NU.digits 26).val = 0 := by
  show ((5 : Nat)^25 / 5^26) % 5 = 0
  -- 5^25 / 5^26 = 0 since 5^25 < 5^26.
  rw [Nat.div_eq_of_lt (by decide : (5 : Nat)^25 < 5^26)]

/-- Digit-24 of `5^25` in base 5 is `0`. -/
theorem canonical_5adic_NU_digit_24 :
    (canonical_5adic_NU.digits 24).val = 0 := by
  show ((5 : Nat)^25 / 5^24) % 5 = 0
  decide

/-- Digit-2 of `5^25` in base 5 is `0` (a low-position smoke). -/
theorem canonical_5adic_NU_digit_2 :
    (canonical_5adic_NU.digits 2).val = 0 := by
  show ((5 : Nat)^25 / 5^2) % 5 = 0
  decide

/-! ## Other canonical 5-adic elements -/

/-- The 5-adic lift of `5` itself — has digit 1 at position 1
    and zero elsewhere. -/
def canonical_5adic_p : ZpSeq 5 :=
  ZpSeq.digits_of_nat 5 (by decide) 5

/-- Digit-0 of `5` in base 5 is `0`. -/
theorem canonical_5adic_p_digit_0 :
    (canonical_5adic_p.digits 0).val = 0 := by decide

/-- Digit-1 of `5` in base 5 is `1`. -/
theorem canonical_5adic_p_digit_1 :
    (canonical_5adic_p.digits 1).val = 1 := by decide

/-- Digit-2 of `5` in base 5 is `0`. -/
theorem canonical_5adic_p_digit_2 :
    (canonical_5adic_p.digits 2).val = 0 := by decide

/-! ## ResolutionLimit anchor — first 25 digits are zero

The canonical 5-adic lift `canonical_5adic_NU = digits_of_nat 5 (5^25)`
satisfies `trunc n = 0` for all `n ≤ 25`, since `5^25 % 5^n = 0`
whenever `5^n ∣ 5^25`.

Combined with `digits_of_nat_trunc`, this is the **DRLT anchor**:
the finite-resolution lattice (`N_U = 5^25`) maps faithfully into
the first 25 levels of the 5-adic lift.
-/

/-- `5^a ∣ 5^b` for `a ≤ b` — PURE via induction on `b`. -/
private theorem pow_dvd_pow_5 (a : Nat) :
    ∀ b, a ≤ b → 5^a ∣ (5 : Nat)^b
  | 0, h => by
    have ha : a = 0 := Nat.le_zero.mp h
    rw [ha]
    exact ⟨1, by rw [Nat.pow_zero, Nat.one_mul]⟩
  | b + 1, h => by
    cases hcase : Nat.decEq a (b + 1) with
    | isTrue heq =>
      exact ⟨1, by rw [heq, Nat.mul_one]⟩
    | isFalse hne =>
      have hlt : a < b + 1 := Nat.lt_of_le_of_ne h hne
      have hle : a ≤ b := Nat.le_of_lt_succ hlt
      obtain ⟨q, hq⟩ := pow_dvd_pow_5 a b hle
      refine ⟨q * 5, ?_⟩
      rw [Nat.pow_succ, hq, E213.Tactic.NatHelper.mul_assoc]

/-- **DRLT anchor**: for any `n ≤ 25`, the 5-adic lift of `N_U = 5^25`
    truncates to zero at level `n`.  Equivalent to the assertion
    that `5^n ∣ 5^25` makes the first `n` digits of the canonical
    embedding all zero. -/
theorem canonical_5adic_NU_trunc_le_25 (n : Nat) (h : n ≤ 25) :
    canonical_5adic_NU.trunc n = 0 := by
  rw [show canonical_5adic_NU.trunc n = (5 : Nat)^25 % 5^n from
        ZpSeq.digits_of_nat_trunc 5 (by decide) (5^25) n]
  -- 5^n ∣ 5^25 ⟹ 5^25 % 5^n = 0.
  obtain ⟨q, hq⟩ : 5^n ∣ (5 : Nat)^25 := pow_dvd_pow_5 n 25 h
  rw [hq]
  exact E213.Tactic.NatHelper.mul_mod_right (5^n) q

end E213.Lib.Math.Padic
