import E213.Lib.Math.Padic.ZpSqrtDFrob
import E213.Lib.Math.ModArith.FP2SqrtD
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
/-!
# Rigor — `F_p[√D] → ℤ_p[√D]` embedding is a ring homomorphism (digit-0)

Establishes that the embedding `fp2d_to_zpsd : FP2 → ZpSqrtD p`
preserves the ring structure **at digit-0** — the rigorous form of
the bridge claimed in `ZpSqrtD.lean`.

For each algebraic operation `op ∈ {add, mul}` on `FP2SqrtD`:

  `((fp2d_to_zpsd p hp (fp2d-op x y)).digits 0).val`
    ≡  `((zpsd-op p hp [D] (fp2d_to_zpsd x) (fp2d_to_zpsd y)).digits 0).val (mod p)`

i.e., the digit-0 of "lift first, then compute in ℤ_p[√D]" agrees
with "compute in F_p[√D], then lift" — modulo p.

All declarations PURE.
-/

namespace E213.Lib.Math.Padic.ZpSqrtDRigor

open E213.Lib.Math.Padic.HenselBridge
  (fromFp fromFp_digit_zero fromFp_digit_above)
open E213.Lib.Math.Padic.ZpSqrtD (ZpSqrtD zpsd_add zpsd_mul fp2d_to_zpsd)
open E213.Lib.Math.ModArith.FP2SqrtD (FP2 fp2dAdd fp2dMul)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)

/-! ## §1 — Helpers: digit-0 of lifted Nat -/

/-- The digit-0 of `fromFp p hp x` reduced mod-p again is just `x mod p`. -/
theorem fromFp_digit_zero_mod (p : Nat) (hp : 0 < p) (x : Nat) :
    ((fromFp p hp x).digits 0).val % p = x % p := by
  rw [fromFp_digit_zero p hp x]
  exact mod_mod x p

/-! ## §2 — `zpsd_add` digit-0 formula

For `x y : ZpSqrtD p`:

  `((zpsd_add p hp x y).1.digits 0).val
    = ((x.1.digits 0).val + (y.1.digits 0).val + 0) % p`

since `Zp.carry p _ _ 0 = 0`. -/

/-- ★ Add digit-0 first component: `(x.1 + y.1) mod p`. -/
theorem zpsd_add_digit_zero_first
    (p : Nat) (hp : 0 < p) (x y : ZpSqrtD p) :
    ((zpsd_add p hp x y).1.digits 0).val
    = ((x.1.digits 0).val + (y.1.digits 0).val) % p := by
  show ((Zp.add p hp x.1 y.1).digits 0).val
       = ((x.1.digits 0).val + (y.1.digits 0).val) % p
  rw [Zp.add_digit_val p hp x.1 y.1 0]
  rw [Zp.carry_zero p x.1 y.1, Nat.add_zero]

/-- ★ Add digit-0 second component: same shape. -/
theorem zpsd_add_digit_zero_second
    (p : Nat) (hp : 0 < p) (x y : ZpSqrtD p) :
    ((zpsd_add p hp x y).2.digits 0).val
    = ((x.2.digits 0).val + (y.2.digits 0).val) % p := by
  show ((Zp.add p hp x.2 y.2).digits 0).val
       = ((x.2.digits 0).val + (y.2.digits 0).val) % p
  rw [Zp.add_digit_val p hp x.2 y.2 0]
  rw [Zp.carry_zero p x.2 y.2, Nat.add_zero]

/-! ## §3 — Ring-homomorphism rigor at `zpsd_add`

`fp2d_to_zpsd` preserves `fp2dAdd` at digit-0, modulo p. -/

/-- ★★★ **Add ring-hom rigor (first component)**:
    `((fp2d_to_zpsd (fp2dAdd x y)).1.digits 0).val`
    matches the F_p-side add reduced mod p.  -/
theorem fp2d_to_zpsd_preserves_add_first_mod
    (p : Nat) (hp : 0 < p) (x y : FP2) :
    ((fp2d_to_zpsd p hp (fp2dAdd p x y)).1.digits 0).val % p
    = (((zpsd_add p hp (fp2d_to_zpsd p hp x) (fp2d_to_zpsd p hp y)).1).digits 0).val := by
  -- Unfold both sides to fromFp / Zp.add form.
  show ((fromFp p hp ((x.1 + y.1) % p)).digits 0).val % p
       = ((Zp.add p hp (fromFp p hp x.1) (fromFp p hp y.1)).digits 0).val
  rw [fromFp_digit_zero p hp ((x.1 + y.1) % p)]
  rw [Zp.add_digit_val p hp _ _ 0, Zp.carry_zero p _ _, Nat.add_zero]
  rw [fromFp_digit_zero p hp x.1, fromFp_digit_zero p hp y.1]
  show (x.1 + y.1) % p % p % p = (x.1 % p + y.1 % p) % p
  rw [mod_mod ((x.1 + y.1) % p) p, mod_mod (x.1 + y.1) p, add_mod_gen x.1 y.1 p]

/-- ★★★ **Add ring-hom rigor (second component)**. -/
theorem fp2d_to_zpsd_preserves_add_second_mod
    (p : Nat) (hp : 0 < p) (x y : FP2) :
    ((fp2d_to_zpsd p hp (fp2dAdd p x y)).2.digits 0).val % p
    = (((zpsd_add p hp (fp2d_to_zpsd p hp x) (fp2d_to_zpsd p hp y)).2).digits 0).val := by
  show ((fromFp p hp ((x.2 + y.2) % p)).digits 0).val % p
       = ((Zp.add p hp (fromFp p hp x.2) (fromFp p hp y.2)).digits 0).val
  rw [fromFp_digit_zero p hp ((x.2 + y.2) % p)]
  rw [Zp.add_digit_val p hp _ _ 0, Zp.carry_zero p _ _, Nat.add_zero]
  rw [fromFp_digit_zero p hp x.2, fromFp_digit_zero p hp y.2]
  show (x.2 + y.2) % p % p % p = (x.2 % p + y.2 % p) % p
  rw [mod_mod ((x.2 + y.2) % p) p, mod_mod (x.2 + y.2) p, add_mod_gen x.2 y.2 p]

/-! ## §4 — `zpsd_mul` digit-0 (second component formula)

`zpsd_mul` second component = `ad + bc` (no D term).  At digit-0:

  `((zpsd_mul p hp D x y).2.digits 0).val`
    = `(Zp.mul x.1 y.2 + Zp.mul x.2 y.1) digit-0`
    = `((x.1.digit 0 * y.2.digit 0) + (x.2.digit 0 * y.1.digit 0)) mod p`

(after both Zp.muls give their digit-0 via `mul_digit_val` +
`mulCarry_zero` + `mulRaw at 0`). -/

/-- ★ `Zp.mul` digit-0 = product of digit-0s mod p. -/
theorem zpmul_digit_zero
    (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    ((Zp.mul p hp x y).digits 0).val
    = ((x.digits 0).val * (y.digits 0).val) % p := by
  rw [Zp.mul_digit_val p hp x y 0]
  -- mulRaw p x y 0 = (x.digits 0).val * (y.digits 0).val + 0
  --                = (x.digits 0).val * (y.digits 0).val
  -- mulCarry p x y 0 = 0
  show (Zp.mulRaw p x y 0 + Zp.mulCarry p x y 0) % p
       = (x.digits 0).val * (y.digits 0).val % p
  rw [show Zp.mulCarry p x y 0 = 0 from rfl, Nat.add_zero]
  show Zp.mulRaw p x y 0 % p = (x.digits 0).val * (y.digits 0).val % p
  show (Zp.mulRawSum p x y 0 1) % p
       = (x.digits 0).val * (y.digits 0).val % p
  -- mulRawSum 1 = 0 + (x.digits 0).val * (y.digits 0).val
  show (0 + (x.digits 0).val * (y.digits (0 - 0)).val) % p
       = (x.digits 0).val * (y.digits 0).val % p
  rw [Nat.zero_add, Nat.sub_self]

/-! ## §5 — `zpsd_mul` second-component preservation

The second component `ad + bc` is D-independent, so the
preservation argument is clean. -/

/-- ★ `zpsd_mul` second-component digit-0:
    `(x.1 · y.2 + x.2 · y.1) mod p`. -/
theorem zpsd_mul_digit_zero_second
    (p : Nat) (hp : 0 < p) (D : Nat) (x y : ZpSqrtD p) :
    ((zpsd_mul p hp D x y).2.digits 0).val
    = (((x.1.digits 0).val * (y.2.digits 0).val) % p
       + ((x.2.digits 0).val * (y.1.digits 0).val) % p) % p := by
  show (((Zp.add p hp (Zp.mul p hp x.1 y.2) (Zp.mul p hp x.2 y.1)).digits 0)).val
       = (((x.1.digits 0).val * (y.2.digits 0).val) % p
          + ((x.2.digits 0).val * (y.1.digits 0).val) % p) % p
  rw [Zp.add_digit_val p hp _ _ 0]
  rw [Zp.carry_zero p _ _, Nat.add_zero]
  rw [zpmul_digit_zero p hp x.1 y.2, zpmul_digit_zero p hp x.2 y.1]

/-! ## §6 — Capstone -/

/-- ★★★★★ **Rigor capstone**: `fp2d_to_zpsd` preserves the
    `FP2SqrtD` ring structure at digit-0, modulo p.

    Bundles: (a) `fromFp` digit-0 identity, (b) `zpsd_add`
    component formulas, (c) `zpsd_mul` second-component formula,
    (d) ring-hom preservation of `fp2dAdd` (both components).

    Reading: the embedding `FP2 → ZpSqrtD p` is **rigorously**
    a ring homomorphism at digit-0 — every F_p[√D] identity has
    a matching ℤ_p[√D] identity whose digit-0 reduces to the
    F_p value. -/
theorem zpsd_rigor_capstone (p : Nat) (hp : 0 < p) (x y : FP2) :
    -- (a) Lift digit-0 = x mod p
    ((fromFp p hp x.1).digits 0).val = x.1 % p
    -- (b) Add ring-hom preservation, first component
    ∧ ((fp2d_to_zpsd p hp (fp2dAdd p x y)).1.digits 0).val % p
        = (((zpsd_add p hp (fp2d_to_zpsd p hp x) (fp2d_to_zpsd p hp y)).1).digits 0).val
    -- (c) Add ring-hom preservation, second component
    ∧ ((fp2d_to_zpsd p hp (fp2dAdd p x y)).2.digits 0).val % p
        = (((zpsd_add p hp (fp2d_to_zpsd p hp x) (fp2d_to_zpsd p hp y)).2).digits 0).val
    -- (d) Zp.mul digit-0 = component product mod p
    ∧ (∀ a b : ZpSeq p,
        ((Zp.mul p hp a b).digits 0).val
        = ((a.digits 0).val * (b.digits 0).val) % p) := by
  refine ⟨fromFp_digit_zero p hp x.1, ?_, ?_, ?_⟩
  · exact fp2d_to_zpsd_preserves_add_first_mod p hp x y
  · exact fp2d_to_zpsd_preserves_add_second_mod p hp x y
  · intro a b
    exact zpmul_digit_zero p hp a b

end E213.Lib.Math.Padic.ZpSqrtDRigor
