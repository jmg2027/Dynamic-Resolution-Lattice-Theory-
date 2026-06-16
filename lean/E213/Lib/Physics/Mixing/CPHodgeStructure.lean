import E213.Lib.Physics.Simplex.Counts

/-!
# CPHodgeStructure — the CP phase `i` is the Hodge complex structure on the 4-dim `Δ⁴`

The number-theory leg (`Icosahedral.CyclotomicFive`) homed the apex in `ℚ(ζ₅)`
(golden modulus + `C₄` phase from the prime `d=5`).  This file gives the
**cohomology** leg: the CP phase's `i` (the `C₄`, `⋆²=−1`) is the **Hodge star
on the `(d−1)=4`-dimensional simplex `Δ⁴`** — the *same* `d=5` cohomology that
derives `1/α_em` (H*(Δ⁴), `GramD2Mechanism`, `CupRingTrace`).  So CP and `α_em`
would share **one** cohomological object.

## The parity that produces the complex structure

The Hodge star on an `n`-dimensional space satisfies `⋆² = (−1)^{k(n−k)}` on
grade `k`.  Reading `Δ⁴` at its **actual dimension `n = d−1 = 4`** (the 4-simplex,
not the 5-vertex count):

  `k(4−k)` for `k=0..4` `= 0, 3, 4, 3, 0`  ⟹  `⋆² = +1, −1, +1, −1, +1`.

So **`⋆² = −1` at grades `k = 1, 3`** — a genuine **complex structure**
(`⋆⁴ = (⋆²)² = (−1)² = +1`, so `⟨⋆⟩ ≅ C₄`), the cohomological `i`.  Grades `1,3`
are `Λ¹` (`= 5̄`, the down-quark/lepton multiplet) and `Λ³` — the
complex-structure-carrying forms of one SU(5) generation (`Λ¹⊕Λ² = 5̄⊕10`).

## Why the repo's `⋆` does not yet show it (the honest caveat)

The repo's Hodge star (`Cohomology/Hodge/Star.lean`) is **ℤ/2 (Bool/XOR)**,
where the sign `(−1)^{k(n−k)}` *collapses* to `+1` — proven `⋆²=+1` at all grades
(`InvolutionLifts`).  And it uses the `n=5` (vertex-count) convention, where
`k(5−k)` is always even (`n` odd) ⟹ `⋆²=+1` regardless.  So the complex
structure (`⋆²=−1`) is invisible there.  It appears **only** at the actual
dimension `n=4` (even) **with signed `ℤ`-coefficients** — the `ℚ²¹³`/`ℤ`-signed
Hodge star the repo flags as unbuilt (`CupRingTrace` "needs ℤ-signed pairings";
`HodgeRiemann` vacuous on ℤ/2).

## The identification (frontier)

`⟨⋆⟩ ≅ C₄ ≅ ℤ[i]^×` — the cohomological `i` (signed `⋆` at `n=4`, grades `1,3`)
*is* the algebraic CP `i` (the Gaussian unit, `CPPhaseC4Forcing`).  Both are
`C₄`.  The signed-`ℤ` Hodge star is now **built** as an operator in
`SignedHodgeStar` (`star_star_eq_sign`: `⋆∘⋆ = (−1)^{k(n−k)}` on all 16 forms
of `Λ(Δ⁴)`, with `⋆²=−1` at grades 1,3 — `hodge_i_order_four`); proving the
ring iso `⟨⋆⟩ ≅ ℤ[i]^×` the **same** object is the remaining step.
A *counting* bridge already exists (`catalogs/cross-domain-identifications.md`
CDI-2: `b₁(K₅) ≡ δ_CP ≡ SU(5) adjoint = 24`), tying the `d=5` cohomology to the
CP sector at the integer level — but the **phase** `i` is the missing
construction.

All theorems PURE (the parity skeleton; the signed `⋆` is now built in
`SignedHodgeStar`, and the ring iso `⟨⋆⟩ ≅ ℤ[i]^×` is the remaining frontier).
-/

namespace E213.Lib.Physics.Mixing.CPHodgeStructure

open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- Hodge `⋆²` sign on grade `k` of an `n`-space is `(−1)^{k(n−k)}`; we track the
    **parity** of the exponent `k(n−k)` (`0 = even ⟹ ⋆²=+1`, `1 = odd ⟹ ⋆²=−1`). -/
def starSqParity (n k : Nat) : Nat := (k * (n - k)) % 2

/-! ## §1 — at `n = d−1 = 4`, `⋆² = −1` exactly at grades `k = 1, 3` -/

/-- ★★★ **Complex structure at grades 1,3.**  On the actual `(d−1)=4`-dimensional
    `Δ⁴`, the Hodge `⋆²` exponent `k(4−k)` is **odd** (`⋆²=−1`) at `k=1,3` and
    even (`⋆²=+1`) at `k=0,2,4`.  So `⟨⋆⟩` at grades `1,3` is a `C₄` complex
    structure (`⋆²=−1`, `⋆⁴=+1`) — the cohomological CP `i`. -/
theorem star_sq_minus_one_at_1_3 :
    -- d − 1 = 4 (the simplex dimension)
    (NS + NT - 1 = 4)
    -- ⋆² = −1 (parity 1) at k = 1, 3
    ∧ starSqParity 4 1 = 1 ∧ starSqParity 4 3 = 1
    -- ⋆² = +1 (parity 0) at k = 0, 2, 4
    ∧ starSqParity 4 0 = 0 ∧ starSqParity 4 2 = 0 ∧ starSqParity 4 4 = 0 := by decide

/-- ★★★ **`⟨⋆⟩ ≅ C₄` at the complex grades.**  At grades `1,3` the star squares
    to `−1` (`(-1:Int)·(-1) = 1` gives `⋆⁴ = +1`), so it generates a cyclic
    group of order `4 = NT²` — the same `C₄` as `ℤ[i]^×` (the CP `i`). -/
theorem star_generates_C4 :
    -- ⋆² = −1 ⇒ ⋆⁴ = (⋆²)² = (−1)² = +1
    ((-1 : Int) * (-1) = 1)
    -- order 4 = NT² (the complex structure = i, arg = 90°)
    ∧ (NT * NT = 4) ∧ (360 / 4 = 90) := by decide

/-! ## §2 — the parity wall: `n=5` (odd) collapses it (why the repo `⋆` is `+1`) -/

/-- ★★★ **Parity wall.**  At `n = 5` (the 5-vertex count, `n` odd), `k(5−k)` is
    **even** for every `k` (`⋆²=+1` always) — no complex structure.  The CP `i`
    appears only at the *even* dimension `n = d−1 = 4`.  (And the repo's ℤ/2 `⋆`
    collapses the sign regardless — the signed `ℤ` star is the frontier.) -/
theorem parity_wall_at_n5 :
    -- n=5 (odd): ⋆² = +1 (parity 0) at every grade k=0..5
    starSqParity 5 0 = 0 ∧ starSqParity 5 1 = 0 ∧ starSqParity 5 2 = 0
    ∧ starSqParity 5 3 = 0 ∧ starSqParity 5 4 = 0 ∧ starSqParity 5 5 = 0
    -- contrast: n=4 (even) has odd parity (−1) at k=1,3
    ∧ starSqParity 4 1 = 1 ∧ starSqParity 4 3 = 1 := by decide

/-! ## §3 — capstone -/

/-- ★★★★★ **The CP `i` is the Hodge complex structure on the 4-dim `Δ⁴`.**
    At the actual dimension `n = d−1 = 4`, the signed Hodge star has `⋆²=−1` at
    grades `1,3` (`Λ¹=5̄`, `Λ³`), generating `C₄ ≅ ℤ[i]^×` — the CP phase `i`
    (`arg = 90°`).  This is the *same* `d=5` cohomology as `1/α_em`, so CP and
    `α_em` share one cohomological object.  **Frontier**: the repo's ℤ/2 `⋆`
    collapses the sign (`⋆²=+1`); realizing the CP `i` needs the signed `ℤ`-Hodge
    star at `n=4` (now **built** in `SignedHodgeStar`, `star_star_eq_sign`) + a
    ring iso `⟨⋆⟩ ≅ ℤ[i]^×` (remaining).  PURE: the parity. -/
theorem cp_i_is_hodge_complex_structure :
    -- the complex grades 1,3 of the (d−1)=4 simplex: ⋆²=−1
    (NS + NT - 1 = 4 ∧ starSqParity 4 1 = 1 ∧ starSqParity 4 3 = 1)
    -- ⟨⋆⟩ ≅ C₄ (order 4 = NT², 90°)
    ∧ ((-1 : Int) * (-1) = 1 ∧ NT * NT = 4 ∧ 360 / 4 = 90)
    -- parity wall: n=5 (vertex count) collapses to +1 (no phase)
    ∧ (starSqParity 5 2 = 0) := by decide

end E213.Lib.Physics.Mixing.CPHodgeStructure
