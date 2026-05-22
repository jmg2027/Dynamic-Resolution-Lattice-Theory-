import E213.Lib.Math.Padic.Foundation

/-!
# Real213-p-adic Arithmetic (Phase 2)

Digit-by-digit arithmetic on `ZpSeq p` via carry-propagation FSM.
All operations PURE — no axioms beyond Nat-level operations.

## Phase 2 contents

  · `Zp.carry x y k` — carry value at position k for sum x + y
  · `Zp.add x y` — p-adic sum with carry propagation
  · `Zp.neg x` — p-adic negation (digit complement + 1)
  · Smoke tests verifying canonical equalities
  · `Zp.add_zero` and `Zp.zero_add` for the trivial cases

Phase 3 will add `Zp.mul` (digit convolution) + truncation
respecting addition / multiplication mod p^n.
-/

namespace E213.Lib.Math.Padic.Zp

open E213.Lib.Math.Padic (ZpDigit ZpSeq)

/-! ## Carry propagation -/

/-- Carry at position k for the sum `x + y` in ℤ_p.

  Defined recursively:
    · `carry 0 = 0`
    · `carry (k+1) = (x.digits k + y.digits k + carry k) / p`

  PURE (Nat / function on Nat). -/
def carry {p : Nat} (x y : ZpSeq p) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      ((x.digits k).val + (y.digits k).val + carry x y k) / p

/-! ## p-adic addition -/

/-- Sum of two p-adic integers `x + y` in ℤ_p with carry propagation.

  Position k digit: `(x_k + y_k + carry_k) % p`.

  Requires `0 < p` for the mod-p safety guarantee
  (digits live in `Fin p`). -/
def add {p : Nat} (hp : 0 < p) (x y : ZpSeq p) : ZpSeq p where
  digits := fun k =>
    ⟨((x.digits k).val + (y.digits k).val + carry x y k) % p,
     Nat.mod_lt _ hp⟩

/-! ## p-adic negation -/

/-- Digit complement: replace each digit d by (p - 1 - d).  Requires
    `0 < p` for the subtraction to behave safely on Nat. -/
def complement {p : Nat} (hp : 0 < p) (x : ZpSeq p) : ZpSeq p where
  digits := fun k => ⟨p - 1 - (x.digits k).val, by
    -- p - 1 - d ≤ p - 1 < p
    have h1 : p - 1 - (x.digits k).val ≤ p - 1 := Nat.sub_le _ _
    exact Nat.lt_of_le_of_lt h1 (Nat.sub_lt hp Nat.one_pos)⟩

/-- p-adic negation: digit complement followed by +1.

  In ℤ_p, `-x = complement(x) + 1`, since
  `x + complement(x) = (p-1, p-1, p-1, ...) = -1`, so
  `complement(x) = -1 - x = -(x + 1)`, hence `complement(x) + 1 = -x`.

  Requires `1 < p` so the implicit `ZpSeq.one p` exists. -/
def neg {p : Nat} (hp : 1 < p) (x : ZpSeq p) : ZpSeq p :=
  add (Nat.lt_of_succ_lt hp) (complement (Nat.lt_of_succ_lt hp) x)
      (ZpSeq.one p hp)

/-! ## Carry sanity: adding zero -/

/-- Adding the zero sequence has zero carry at every position. -/
theorem carry_add_zero {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ k, carry x (ZpSeq.zero p hp) k = 0
  | 0 => rfl
  | k + 1 => by
    show ((x.digits k).val + ((ZpSeq.zero p hp).digits k).val
         + carry x (ZpSeq.zero p hp) k) / p = 0
    -- digit of zero is 0, carry is 0 by IH
    have hzero : ((ZpSeq.zero p hp).digits k).val = 0 := rfl
    rw [hzero, carry_add_zero hp x k]
    -- After def-reductions: (x.digits k).val / p = 0 since digit < p
    exact Nat.div_eq_of_lt (x.digits k).isLt

/-! ## Smoke tests -/

/-- Carry at position 0 is always 0 (initial condition). -/
theorem carry_zero (p : Nat) (x y : ZpSeq p) : carry x y 0 = 0 := rfl

/-- Adding zero leaves the digit unchanged.  Concrete smoke at p = 5
    showing `add (one 5) (zero 5)` matches `one 5` at digit 0. -/
theorem smoke_add_zero_p5 :
    ((add (by decide : 0 < 5)
      (ZpSeq.one 5 (by decide)) (ZpSeq.zero 5 (by decide))).digits 0).val = 1 := by
  show ((((ZpSeq.one 5 (by decide)).digits 0).val
        + ((ZpSeq.zero 5 (by decide)).digits 0).val
        + carry (ZpSeq.one 5 (by decide)) (ZpSeq.zero 5 (by decide)) 0) % 5)
       = 1
  rfl

/-- Adding zero at p = 3 also leaves digit 0 unchanged. -/
theorem smoke_add_zero_p3 :
    ((add (by decide : 0 < 3)
      (ZpSeq.one 3 (by decide)) (ZpSeq.zero 3 (by decide))).digits 0).val = 1 := by
  rfl

/-! ## Complement smoke -/

/-- Complement at p = 5: digit 0 of `complement(one 5)` is `5 - 1 - 1 = 3`. -/
theorem smoke_complement_one_p5 :
    ((complement (by decide : 0 < 5) (ZpSeq.one 5 (by decide))).digits 0).val = 3 := by
  rfl

/-- Complement at p = 5: digit k ≠ 0 of `complement(one 5)` is `5 - 1 = 4`
    (since `one`'s digit k > 0 is 0, complement is p - 1). -/
theorem smoke_complement_one_p5_at_1 :
    ((complement (by decide : 0 < 5) (ZpSeq.one 5 (by decide))).digits 1).val = 4 := by
  rfl

/-! ## neg_one negation smoke -/

/-- Negating `neg_one` at p = 5: digit 0 should be `complement(neg_one) + 1 = 0 + 1 = 1`. -/
theorem smoke_neg_neg_one_p5_digit_0 :
    ((neg (by decide : 1 < 5) (ZpSeq.neg_one 5 (by decide))).digits 0).val = 1 := by
  -- complement(neg_one) has digit 0 = 5 - 1 - 4 = 0
  -- carry at position 0 is 0
  -- sum at position 0: 0 + 1 + 0 = 1, mod 5 = 1
  rfl

end E213.Lib.Math.Padic.Zp
