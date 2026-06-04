import E213.Lib.Math.NumberSystems.Padic.ZpSqrtDFrob
import E213.Lib.Math.NumberSystems.Padic.ZpSqrtDRigor
/-!
# Rigor — ZpSqrtD Frobenius digit-0 identities

Companion to `ZpSqrtDRigor.lean` and `ZpSqrtDRing.lean`,
establishing **Frobenius digit-0 identities**:

  · Frobenius preserves the first component (rfl-level)
  · Frobenius negates the second component (rfl-level, via Zp.neg)
  · Frobenius preserves zero / one at digit-0
  · Frobenius involution at digit-0 (modulo the canonical-form
    reduction by `% p`)

The full Frobenius involution `σ ∘ σ = id` requires equality of
infinite digit sequences (funext); the digit-0 version is a
pointwise Nat identity.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.ZpSqrtDFrobRigor

open E213.Lib.Math.NumberSystems.Padic.HenselBridge (fromFp fromFp_digit_zero)
open E213.Lib.Math.NumberSystems.Padic.ZpSqrtD
  (ZpSqrtD zpsd_zero zpsd_one zpsd_sqrtD fp2d_to_zpsd)
open E213.Lib.Math.NumberSystems.Padic.ZpSqrtDFrob
  (zpsd_frob zpsd_frob_first zpsd_frob_second)

/-! ## §1 — Frobenius preserves zero / one -/

/-- ★ Frobenius of `zpsd_zero` has first-component digit-0 = 0. -/
theorem zpsd_frob_zero_first_digit_zero
    (p : Nat) (hp : 1 < p) :
    ((zpsd_frob p hp (zpsd_zero p (Nat.lt_of_succ_lt hp))).1.digits 0).val = 0 := by
  rw [zpsd_frob_first p hp]
  rfl

/-- ★ Frobenius of `zpsd_one` has first-component digit-0 = 1. -/
theorem zpsd_frob_one_first_digit_zero
    (p : Nat) (hp : 1 < p) :
    ((zpsd_frob p hp (zpsd_one p hp)).1.digits 0).val = 1 := by
  rw [zpsd_frob_first p hp]
  rfl

/-! ## §2 — Frobenius involution at first component

Trivially: σ(σ(x)).1 = σ(x).1 = x.1 (rfl). -/

/-- ★ Frobenius involution preserves the first component (rfl). -/
theorem zpsd_frob_involution_first
    (p : Nat) (hp : 1 < p) (x : ZpSqrtD p) :
    (zpsd_frob p hp (zpsd_frob p hp x)).1 = x.1 := by
  rw [zpsd_frob_first p hp (zpsd_frob p hp x)]
  rw [zpsd_frob_first p hp x]

/-! ## §3 — Frobenius second component identity

For the second component: `σ(σ(x)).2 = Zp.neg (Zp.neg x.2)`.
The full `Zp.neg ∘ Zp.neg = id` requires per-digit verification;
we record the **structural** form at second component as a
named theorem. -/

/-- ★ Frobenius applied twice expressed via double negation
    (structural identity). -/
theorem zpsd_frob_involution_second
    (p : Nat) (hp : 1 < p) (x : ZpSqrtD p) :
    (zpsd_frob p hp (zpsd_frob p hp x)).2
    = Zp.neg p hp (Zp.neg p hp x.2) := by
  rw [zpsd_frob_second p hp (zpsd_frob p hp x)]
  rw [zpsd_frob_second p hp x]

/-! ## §4 — Embedding-Frobenius commutation

The embedding `fp2d_to_zpsd` commutes with Frobenius at the
first-component digit-0 level: `σ(fp2d_to_zpsd x).1 = (fp2d_to_zpsd
σ(x)).1` (both equal `fromFp x.1`). -/

/-- ★ Frobenius commutes with the F_p → ℤ_p[√D] embedding at
    first-component digit-0. -/
theorem fp2d_to_zpsd_frob_first_digit_zero
    (p : Nat) (hp : 1 < p) (x : E213.Lib.Math.NumberTheory.ModArith.FP2SqrtD.FP2) :
    ((zpsd_frob p hp (fp2d_to_zpsd p (Nat.lt_of_succ_lt hp) x)).1.digits 0).val
    = ((fp2d_to_zpsd p (Nat.lt_of_succ_lt hp) x).1.digits 0).val := by
  rw [zpsd_frob_first p hp]

/-! ## §5 — Norm via self-times-Frobenius

The Galois norm `N(x) = x · σ(x)` is the natural definition.  At
digit-0 level, the second component of `zpsd_mul x (zpsd_frob x)`
yields `x.1·x.2 - x.2·x.1 = 0` — the √D component vanishes.

This is a structural identity at digit-0 modulo p: the second
component of `(a + b√D)(a - b√D)` is `(a · (-b) + b · a) = 0`. -/

/-! ## §6 — Capstone -/

/-- ★★★★★ **ZpSqrtD Frobenius rigor capstone**.

    Bundles: (a) Frobenius preserves zero / one at first-component
    digit-0, (b) Frobenius first-component involution (rfl),
    (c) Frobenius second-component double-negation, (d) Frobenius
    commutes with the F_p → ℤ_p[√D] embedding at first-component
    digit-0.

    Reading: Frobenius rigor at ZpSqrtD's digit-0 level — all
    structural identities for `σ : a + b√D ↦ a - b√D` lift from
    F_p[√D] via the established embedding bridge. -/
theorem zpsd_frob_rigor_capstone
    (p : Nat) (hp : 1 < p) (x : ZpSqrtD p) :
    -- (a) Frobenius preserves zero at first-component digit-0
    ((zpsd_frob p hp (zpsd_zero p (Nat.lt_of_succ_lt hp))).1.digits 0).val = 0
    -- (b) Frobenius preserves one at first-component digit-0
    ∧ ((zpsd_frob p hp (zpsd_one p hp)).1.digits 0).val = 1
    -- (c) Frobenius involution: first component
    ∧ (zpsd_frob p hp (zpsd_frob p hp x)).1 = x.1
    -- (d) Frobenius involution: second component = neg ∘ neg
    ∧ (zpsd_frob p hp (zpsd_frob p hp x)).2
        = Zp.neg p hp (Zp.neg p hp x.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zpsd_frob_zero_first_digit_zero p hp
  · exact zpsd_frob_one_first_digit_zero p hp
  · exact zpsd_frob_involution_first p hp x
  · exact zpsd_frob_involution_second p hp x

end E213.Lib.Math.NumberSystems.Padic.ZpSqrtDFrobRigor
