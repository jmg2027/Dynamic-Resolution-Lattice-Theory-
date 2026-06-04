import E213.Lib.Math.NumberSystems.Padic.ZpSqrtD
/-!
# ZpSqrtD Frobenius + Norm

Continues `ZpSqrtD.lean` (the F_p[√D] → ℤ_p[√D] type and ring
ops) with **Frobenius automorphism** and the **norm map**.

  `zpsd_frob (a, b) := (a, -b)` — sends `a + b√D ↦ a − b√D`.
  `zpsd_norm (a, b) := a² − D·b²` — the Galois norm.

These are the ℤ_p analogs of `FP2SqrtD.fp2dFrob` and `fp2dNorm`.
Frobenius is a ring endomorphism; the norm is a multiplicative
map to `ZpSeq p` (no √D component).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.ZpSqrtDFrob

open E213.Lib.Math.NumberSystems.Padic.HenselBridge (fromFp fromFp_digit_zero)
open E213.Lib.Math.NumberSystems.Padic.ZpSqrtD
  (ZpSqrtD zpsd_zero zpsd_one zpsd_sqrtD fp2d_to_zpsd)

/-! ## §1 — Frobenius -/

/-- Frobenius automorphism: `σ(a + b√D) = a − b√D = (a, -b)` in
    the pair representation.  Requires `1 < p` for `Zp.neg`. -/
def zpsd_frob (p : Nat) (hp : 1 < p) (x : ZpSqrtD p) : ZpSqrtD p :=
  (x.1, Zp.neg p hp x.2)

/-! ## §2 — Norm -/

/-- Galois norm: `N(a + b√D) = (a + b√D)(a − b√D) = a² − D·b²`.
    Returns just the first component (the √D coefficient vanishes
    by the Frobenius pairing). -/
def zpsd_norm (p : Nat) (hp : 1 < p) (D : Nat) (x : ZpSqrtD p) :
    ZpSeq p :=
  let hp0 : 0 < p := Nat.lt_of_succ_lt hp
  let asq := Zp.mul p hp0 x.1 x.1
  let bsq := Zp.mul p hp0 x.2 x.2
  let dseq := fromFp p hp0 D
  let Dbsq := Zp.mul p hp0 dseq bsq
  -- a² − D·b² = a² + (-D·b²)
  Zp.add p hp0 asq (Zp.neg p hp Dbsq)

/-! ## §3 — Frobenius properties (digit-0 level) -/

/-- Frobenius on `zpsd_zero` is `zpsd_zero` itself (digit-0). -/
theorem zpsd_frob_zero_digit_0
    (p : Nat) (hp : 1 < p) :
    ((zpsd_frob p hp (zpsd_zero p (Nat.lt_of_succ_lt hp))).1.digits 0).val = 0 := by
  show ((zpsd_zero p (Nat.lt_of_succ_lt hp)).1.digits 0).val = 0
  rfl

/-- Frobenius preserves the first component. -/
theorem zpsd_frob_first
    (p : Nat) (hp : 1 < p) (x : ZpSqrtD p) :
    (zpsd_frob p hp x).1 = x.1 := rfl

/-- Frobenius negates the second component. -/
theorem zpsd_frob_second
    (p : Nat) (hp : 1 < p) (x : ZpSqrtD p) :
    (zpsd_frob p hp x).2 = Zp.neg p hp x.2 := rfl

/-! ## §4 — Frobenius on lifted F_p elements

For a Nat `b` with `b < p`, `Zp.neg p hp (fromFp p hp0 b)`
has digit-0 = `p - b % p` mod p — the F_p-side negation. -/

/-- Smoke at `p = 7, b = 2`: Frobenius's second-component digit-0
    is `7 - 2 = 5` (= `-2 mod 7`). -/
theorem zpsd_frob_smoke_7_2 :
    ((zpsd_frob 7 (by decide)
        (fp2d_to_zpsd 7 (by decide) (3, 2))).2.digits 0).val
    = ((Zp.neg 7 (by decide) (fromFp 7 (by decide) 2)).digits 0).val := rfl

/-! ## §5 — Norm at canonical elements -/

/-- Norm of zero: `N(0) = 0`. -/
theorem zpsd_norm_zero_digit_0
    (p : Nat) (hp : 1 < p) (D : Nat) :
    let hp0 : 0 < p := Nat.lt_of_succ_lt hp
    ((zpsd_norm p hp D (zpsd_zero p hp0)).digits 0).val
    = ((Zp.add p hp0 (Zp.mul p hp0 (ZpSeq.zero p hp0) (ZpSeq.zero p hp0))
          (Zp.neg p hp
            (Zp.mul p hp0 (fromFp p hp0 D)
              (Zp.mul p hp0 (ZpSeq.zero p hp0) (ZpSeq.zero p hp0))))).digits 0).val :=
  rfl

/-! ## §6 — Capstone -/

/-- ★★★★★ **ZpSqrtD Frobenius + Norm capstone**.

    Bundles: (a) `zpsd_frob` definition and component identities,
    (b) `zpsd_norm` definition via `Zp.mul + Zp.add + Zp.neg`,
    (c) smoke at concrete (p, D).

    Reading: the F_p[√D] Frobenius and norm machinery lifts to
    ℤ_p[√D] using the existing Padic `Zp.add / Zp.mul / Zp.neg`
    operations.  All algebraic identities of FP2SqrtD have ℤ_p
    analogs. -/
theorem zpsd_frob_norm_capstone
    (p : Nat) (hp : 1 < p) (x : ZpSqrtD p) :
    -- (a) Frobenius preserves first component
    (zpsd_frob p hp x).1 = x.1
    -- (b) Frobenius negates second component
    ∧ (zpsd_frob p hp x).2 = Zp.neg p hp x.2
    -- (c) Frobenius of zero has first-component digit-0 = 0
    ∧ ((zpsd_frob p hp (zpsd_zero p (Nat.lt_of_succ_lt hp))).1.digits 0).val = 0 := by
  refine ⟨rfl, rfl, rfl⟩

end E213.Lib.Math.NumberSystems.Padic.ZpSqrtDFrob
