import E213.Theory.Raw.Odometer

/-!
# Theory.Raw.OdometerValue — the profinite value: the `+1` is `+1 mod 2ᵏ` on the first `k` bits

`Odometer` builds the `+1` adding machine and its `ℤ`-action.  This file adds the **value** map
`bval k f` (the natural number read off the first `k` bits, LSB-first) and proves the odometer is
literally `+1` with a carry-out: `bval k (odo f) + (carry-out)·2ᵏ = bval k f + 1`
(`bval_odo`) — the profinite statement `odo = (+1 mod 2ᵏ)` in carry-explicit form (no division).

This pins the residue's escape space as `ℤ₂ = lim ℤ/2ᵏ` quantitatively (the `+1` is the
arithmetic successor on each finite truncation) and gives **fixed-point-freeness** of the unit
(`odo_no_fixpoint`: the `+1` never fixes a point — the act of pointing always changes something).
All ∅-axiom (manual `Nat` arithmetic — `omega` and core `Nat.add_mul`/`Nat.mul_assoc` are
propext/`Quot`-tainted, so explicit pure lemmas are used).
-/

namespace E213.Theory.Raw.OdometerValue

open E213.Theory.Raw.Odometer
  (carry odo shift carry_zero carry_succ odo_apply shift_apply carry_shift)

/-- A bit's numeric value: `1` for `true`, `0` for `false`. -/
def bit (b : Bool) : Nat := cond b 1 0

/-- The value of the first `k` bits of `f` (LSB-first): `bval (k+1) f = bit (f 0) + 2·bval k (σf)`. -/
def bval : Nat → (Nat → Bool) → Nat
  | 0,     _ => 0
  | k + 1, f => bit (f 0) + 2 * bval k (shift f)

/-- The carry-out of the first `k` bits, as a value: `2ᵏ` if the carry survives, else `0`. -/
def carryVal (k : Nat) (f : Nat → Bool) : Nat := cond (carry f k) (2 ^ k) 0

theorem bval_succ (k : Nat) (f : Nat → Bool) :
    bval (k + 1) f = bit (f 0) + 2 * bval k (shift f) := rfl

/-- ★★ **`bval` respects pointwise-equal streams** (a `funext`-free congruence). -/
theorem bval_congr : ∀ (k : Nat) {f g : Nat → Bool}, (∀ n, f n = g n) → bval k f = bval k g
  | 0,     _, _, _ => rfl
  | k + 1, f, g, h => by
      have hsh : ∀ n, shift f n = shift g n := fun n => h (n + 1)
      rw [bval_succ, bval_succ, h 0, bval_congr k hsh]

/-- `2 · 2ᵏ = 2^(k+1)` (pure). -/
theorem two_mul_pow (k : Nat) : 2 * 2 ^ k = 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- `2 · (carry-out at `k`) = (carry-out at `k+1`)` (cases on the carry bit). -/
theorem two_mul_cond (c : Bool) (k : Nat) :
    2 * cond c (2 ^ k) 0 = cond c (2 ^ (k + 1)) 0 := by
  cases c with
  | false => rfl
  | true  => exact two_mul_pow k

/-- Pure-`Nat` arithmetic for the low-bit-`0` case: `1 + 2A + 0 = 0 + 2A + 1`. -/
theorem addmix_false (A : Nat) : 1 + 2 * A + 0 = 0 + 2 * A + 1 := by
  rw [Nat.add_zero, Nat.zero_add, Nat.add_comm]

/-- Pure-`Nat` arithmetic for the low-bit-`1` case: given `B + C = D + 1`,
    `0 + 2B + 2C = 1 + 2D + 1`. -/
theorem addmix_true (B C D : Nat) (h : B + C = D + 1) :
    0 + 2 * B + 2 * C = 1 + 2 * D + 1 := by
  rw [Nat.zero_add, ← Nat.mul_add, h, Nat.mul_add, Nat.mul_one,
      Nat.add_comm 1 (2 * D), Nat.add_assoc]

/-- ★★★ **The odometer is `+1` with a carry-out (the profinite successor).**  `bval k (odo f) +
    carryVal k f = bval k f + 1`: the value of the first `k` bits of `f + 1`, plus the carry-out
    `2ᵏ` if the increment overflowed the `k`-bit window, equals `bval k f + 1`.  So `odo` is the
    arithmetic successor on every finite truncation — `odo = (+1 mod 2ᵏ)`, carry-explicit (no
    division).  By induction on `k`, splitting on the low bit `f 0` (carry stops vs propagates,
    `carry_shift`); the arithmetic is pure `Nat`. -/
theorem bval_odo (f : Nat → Bool) : ∀ k, bval k (odo f) + carryVal k f = bval k f + 1
  | 0     => rfl
  | k + 1 => by
      have ih := bval_odo (shift f) k
      cases hf0 : f 0 with
      | false =>
          have hsh : ∀ n, shift (odo f) n = shift f n := fun n => by
            rw [shift_apply, shift_apply, odo_apply, carry_shift, hf0, Bool.false_and,
                Bool.xor_false]
          have hodo0 : odo f 0 = true := by rw [odo_apply, carry_zero, hf0]; rfl
          have hcarry : carryVal (k + 1) f = 0 := by
            show cond (carry f (k + 1)) (2 ^ (k + 1)) 0 = 0
            rw [carry_shift, hf0, Bool.false_and]; rfl
          rw [bval_succ, bval_succ, hodo0, hf0, hcarry, bval_congr k hsh]
          show 1 + 2 * bval k (shift f) + 0 = 0 + 2 * bval k (shift f) + 1
          exact addmix_false _
      | true =>
          have hsh : ∀ n, shift (odo f) n = odo (shift f) n := fun n => by
            rw [shift_apply, odo_apply, odo_apply, carry_shift, hf0, Bool.true_and, shift_apply]
          have hodo0 : odo f 0 = false := by rw [odo_apply, carry_zero, hf0]; rfl
          have hcarry : carryVal (k + 1) f = 2 * carryVal k (shift f) := by
            show cond (carry f (k + 1)) (2 ^ (k + 1)) 0 = 2 * cond (carry (shift f) k) (2 ^ k) 0
            rw [carry_shift, hf0, Bool.true_and, two_mul_cond]
          rw [bval_succ, bval_succ, hodo0, hf0, hcarry, bval_congr k hsh]
          show 0 + 2 * bval k (odo (shift f)) + 2 * carryVal k (shift f)
             = 1 + 2 * bval k (shift f) + 1
          exact addmix_true _ _ _ ih

/-- ★★★ **The residue unit `+1` is fixed-point-free.**  `odo f 0 ≠ f 0`: incrementing always flips
    the least-significant bit, so the `+1` fixes no stream — the act of pointing always changes
    something (the `k = 1` case of the `ℤ`-action's freeness). -/
theorem odo_no_fixpoint (f : Nat → Bool) : odo f 0 ≠ f 0 := by
  rw [odo_apply, carry_zero]
  cases f 0 <;> decide

end E213.Theory.Raw.OdometerValue
