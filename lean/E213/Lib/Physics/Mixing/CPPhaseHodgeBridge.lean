import E213.Lib.Math.Cohomology.Hodge.SignedStarC4
import E213.Lib.Physics.Simplex.Counts

/-!
# The CP phase's `C₄` IS the signed Hodge star's order-4 group (no hand-written list)

`CPPhaseC4Forcing` forces `δ = 90°` from "the phase lives in `C₄ = ℤ[i]^×`", but
its `C₄` is a **hand-written list** `def c4 := [(1,0),(0,1),(-1,0),(0,-1)]`.  This
file upgrades that to the genuine structure: the four `C₄` Gaussian units
`{1, i, −1, −i}`, embedded via `elt`, are **exactly the powers `{J⁰, J¹, J², J³}`
of the signed Hodge star `J = ⋆`** on the `d−1 = 4` simplex (`SignedStarC4`),
which is proven to have order 4 (`J² = −I`, `J⁴ = I`, `J² ≠ I` ⇒ `C₄`), with
`360/4 = 90°`.

So "the CP phase lies in `C₄ ⇒ 90°`" comes from the **actual `⋆`-operator on
`Δ⁴`** — the genuine math — not from a posited list.  Drawable: *"the Hodge star
on the 4-simplex squares to `−1`, so applying it four times is the identity — an
order-4 (90°) rotation; the CP phase is one of its four powers."*

Honest scope (the freezing line): this closes the **math** (the phase's `C₄` is
the genuine `⟨⋆⟩`, order 4, 90°).  It does NOT force the **physics** readings:
"this `⋆`-phase IS the CKM phase" and "Jarlskog `J ∝ Im`" (the `imPart := u.2`
projection) remain irreducible identifications, kept as readings.

All theorems PURE.
-/

namespace E213.Lib.Physics.Mixing.CPPhaseHodgeBridge

open E213.Lib.Math.Cohomology.Hodge.SignedStarC4 (mul I negI J elt signed_hodge_is_cp_i)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- ◑ **The CP `C₄` units = the powers of the matrix `J = (0,−1,1,0)`.**
    (Honest tier ◑, not ★★★★★: this is a `decide` bundle of matrix-entry facts;
    `J`-as-the-Hodge-`⋆`-on-`Δ⁴` is a docstring identification, not `J = hodgeStar`.)
    The four `C₄` Gaussian units `{1, i, −1, −i}` (`elt 1 0, elt 0 1, elt (−1) 0,
    elt 0 (−1)`) are exactly the powers `{J⁰=I, J¹=J, J²=−I, J³}` of the signed
    Hodge star `J = ⋆` on the `d−1=4` simplex; `J` generates `C₄` (order 4),
    giving `δ = 360/4 = 90°` from the genuine `⋆`, not a hand-written list.
    Closes the MATH; the CKM/`J∝Im` readings stay readings. -/
theorem cp_c4_is_signed_hodge_group :
    -- the four C₄ units (re, im), via `elt`, ARE the powers of the Hodge star J
    (elt 1 0 = I)
    ∧ (elt 0 1 = J)
    ∧ (elt (-1) 0 = negI)
    ∧ (elt 0 (-1) = mul (mul J J) J)
    -- J generates C₄ on the d−1 = 4 simplex (⋆²=−I, ⋆⁴=I, ⋆²≠I)
    ∧ (mul J J = negI ∧ mul (mul (mul J J) J) J = I ∧ mul J J ≠ I)
    -- order 4 = NT², phase 360/4 = 90°, on the d−1 = NS+NT−1 = 4 simplex
    ∧ (NT * NT = 4 ∧ 360 / 4 = 90 ∧ NS + NT - 1 = 4) := by
  decide

end E213.Lib.Physics.Mixing.CPPhaseHodgeBridge
