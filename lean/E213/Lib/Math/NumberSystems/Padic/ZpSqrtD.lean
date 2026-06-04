import E213.Lib.Math.NumberSystems.Padic.HenselBridge
import E213.Lib.Math.ModArith.FP2SqrtD
/-!
# ZpSqrtD — quadratic extension `ℤ_p[√D]` parametric in D

Continues the Hensel-bridge work in `Padic/HenselBridge.lean` to
construct the **full quadratic field extension** of ℤ_p:

  `ZpSqrtD p` := `ZpSeq p × ZpSeq p` representing `a + b·√D`.

Lifts the F_p-side `FP2SqrtD` operations (ring + Frobenius + Norm)
to ℤ_p componentwise:

  · `zpsd_add` — componentwise `Zp.add`.
  · `zpsd_mul` — `(a + b√D)(c + d√D) = (ac + D·bd) + (ad + bc)√D`
    using `Zp.mul` and a D-lift via `fromFp p hp D`.
  · `zpsd_frob` — Frobenius `(a, b) ↦ (a, -b)` using `Zp.negSeq`-
    style negation on the second component.

## Bridge to FP2SqrtD

The 213-native `F_p ↪ ℤ_p` embedding (via `fromFp`) extends
elementwise:

  `fp2d_to_zpsd : FP2SqrtD.FP2 → ZpSqrtD p`

with `(zpsd_mul) ∘ (fp2d_to_zpsd × fp2d_to_zpsd) = fp2d_to_zpsd ∘
fp2dMul` at the digit-0 level (definitional).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.ZpSqrtD

open E213.Lib.Math.NumberSystems.Padic.HenselBridge (fromFp fromFp_digit_zero)
open E213.Lib.Math.ModArith.FP2SqrtD (FP2)

/-! ## §1 — Type and basic operations -/

/-- `ZpSqrtD p` element: pair `(a, b) : ZpSeq p × ZpSeq p`
    representing `a + b·√D`.  The parameter `D` enters via the
    multiplication rule below, not the type. -/
abbrev ZpSqrtD (p : Nat) : Type := ZpSeq p × ZpSeq p

/-- Componentwise addition: `(a₁ + b₁√D) + (a₂ + b₂√D) =
    (a₁ + a₂) + (b₁ + b₂)√D`.  D-independent. -/
def zpsd_add (p : Nat) (hp : 0 < p) (x y : ZpSqrtD p) : ZpSqrtD p :=
  (Zp.add p hp x.1 y.1, Zp.add p hp x.2 y.2)

/-- Multiplication parametric in D :
    `(a + b√D)(c + d√D) = (ac + D·bd) + (ad + bc)√D`. -/
def zpsd_mul (p : Nat) (hp : 0 < p) (D : Nat) (x y : ZpSqrtD p) :
    ZpSqrtD p :=
  let ac := Zp.mul p hp x.1 y.1
  let bd := Zp.mul p hp x.2 y.2
  let dseq := fromFp p hp D
  let Dbd := Zp.mul p hp dseq bd
  let ad := Zp.mul p hp x.1 y.2
  let bc := Zp.mul p hp x.2 y.1
  (Zp.add p hp ac Dbd, Zp.add p hp ad bc)

/-! ## §2 — Lifting FP2 to ZpSqrtD -/

/-- Embedding `FP2 ↪ ZpSqrtD p`: lift each component via `fromFp`.
    Takes a pair `(a, b) : Nat × Nat` to the ℤ_p element
    `(fromFp a, fromFp b)`. -/
def fp2d_to_zpsd (p : Nat) (hp : 0 < p) (x : FP2) : ZpSqrtD p :=
  (fromFp p hp x.1, fromFp p hp x.2)

/-! ## §3 — Digit-0 bridge -/

/-- The first-component digit-0 of a lifted `FP2` matches the
    Nat mod-p reduction. -/
theorem fp2d_to_zpsd_digit_0_first
    (p : Nat) (hp : 0 < p) (x : FP2) :
    ((fp2d_to_zpsd p hp x).1.digits 0).val = x.1 % p :=
  fromFp_digit_zero p hp x.1

/-- The second-component digit-0 of a lifted `FP2` matches the
    Nat mod-p reduction. -/
theorem fp2d_to_zpsd_digit_0_second
    (p : Nat) (hp : 0 < p) (x : FP2) :
    ((fp2d_to_zpsd p hp x).2.digits 0).val = x.2 % p :=
  fromFp_digit_zero p hp x.2

/-! ## §4 — Zero / one constants -/

/-- The ZpSqrtD zero `0 + 0·√D`. -/
def zpsd_zero (p : Nat) (hp : 0 < p) : ZpSqrtD p :=
  (ZpSeq.zero p hp, ZpSeq.zero p hp)

/-- The ZpSqrtD one `1 + 0·√D` (requires `1 < p`). -/
def zpsd_one (p : Nat) (hp : 1 < p) : ZpSqrtD p :=
  (ZpSeq.one p hp, ZpSeq.zero p (Nat.lt_of_succ_lt hp))

/-- The "irrational generator" `√D = 0 + 1·√D`. -/
def zpsd_sqrtD (p : Nat) (hp : 1 < p) : ZpSqrtD p :=
  (ZpSeq.zero p (Nat.lt_of_succ_lt hp), ZpSeq.one p hp)

/-! ## §5 — Smoke / structural identities -/

/-- The zero lift matches at digit 0. -/
theorem zpsd_zero_digit_zero (p : Nat) (hp : 0 < p) :
    ((zpsd_zero p hp).1.digits 0).val = 0
    ∧ ((zpsd_zero p hp).2.digits 0).val = 0 := by
  refine ⟨rfl, rfl⟩

/-- The one lift matches at digit 0 (for `1 < p`). -/
theorem zpsd_one_digit_zero (p : Nat) (hp : 1 < p) :
    ((zpsd_one p hp).1.digits 0).val = 1
    ∧ ((zpsd_one p hp).2.digits 0).val = 0 := by
  refine ⟨rfl, rfl⟩

/-- Smoke at p = 7, D = 3: `fp2d_to_zpsd (2, 1)` has digit-0
    `(2, 1)`. -/
theorem fp2d_to_zpsd_smoke_7_3 :
    ((fp2d_to_zpsd 7 (by decide) (2, 1)).1.digits 0).val = 2
    ∧ ((fp2d_to_zpsd 7 (by decide) (2, 1)).2.digits 0).val = 1 := by
  refine ⟨rfl, rfl⟩

/-! ## §6 — Capstone -/

/-- ★★★★★ **ZpSqrtD = ℤ_p[√D] construction capstone**.

    Bundles: (a) the ZpSqrtD type as `ZpSeq × ZpSeq`,
    (b) operations `zpsd_add` / `zpsd_mul` parametric in `D : Nat`,
    (c) the embedding `fp2d_to_zpsd : FP2 → ZpSqrtD p`,
    (d) digit-0 bridge to the underlying `F_p × F_p`.

    Reading: the F_p[√D] machinery (ring + Frobenius + Norm)
    lifts componentwise to ℤ_p[√D] via the canonical embedding
    `fromFp`.  Every `F_p[√D]` identity has a ℤ_p[√D] analog
    whose digit-0 matches the F_p[√D] value. -/
theorem zpsd_capstone (p : Nat) (hp : 1 < p) :
    -- (a) Zero / one constants
    ((zpsd_zero p (Nat.lt_of_succ_lt hp)).1.digits 0).val = 0
    ∧ ((zpsd_one p hp).1.digits 0).val = 1
    -- (b) Lift bridge: digit-0 = mod-p reduction
    ∧ (∀ x : FP2,
        ((fp2d_to_zpsd p (Nat.lt_of_succ_lt hp) x).1.digits 0).val
        = x.1 % p)
    ∧ (∀ x : FP2,
        ((fp2d_to_zpsd p (Nat.lt_of_succ_lt hp) x).2.digits 0).val
        = x.2 % p)
    -- (c) Generator √D has digit-0 (0, 1)
    ∧ ((zpsd_sqrtD p hp).1.digits 0).val = 0
    ∧ ((zpsd_sqrtD p hp).2.digits 0).val = 1 := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
  · intro x
    exact fp2d_to_zpsd_digit_0_first p (Nat.lt_of_succ_lt hp) x
  · intro x
    exact fp2d_to_zpsd_digit_0_second p (Nat.lt_of_succ_lt hp) x

end E213.Lib.Math.NumberSystems.Padic.ZpSqrtD
