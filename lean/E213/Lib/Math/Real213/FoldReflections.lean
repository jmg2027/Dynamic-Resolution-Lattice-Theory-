import E213.Lib.Math.Real213.ModularElliptic

/-!
# The two folds are reflections; their product is the founding elliptic swap

`Lens/Number/FoldKlein` showed, on the four-point fixture, that negation `negQ` and reciprocal `recQ`
generate a Klein four-group whose fixed-point-free antipode `bothSwap = z ↦ −1/z` is the founding
elliptic swap `S`.  That cross-frame link is narrative on the fixture; here it is a **matrix theorem**.

The two founding folds are the integer `2×2` matrices

  - `N = [[−1, 0], [0, 1]]` — negation `z ↦ −z` (the additive fold), and
  - `R = [[0, 1], [1, 0]]` — reciprocal `z ↦ 1/z` (the multiplicative fold).

Both are **involutions** (`N² = R² = I`) with **determinant `−1`** — orientation-reversing
*reflections*.  Their product is the founding elliptic swap

  `N · R = S = [[0, −1], [1, 0]]`   (`ModularElliptic.S`, `z ↦ −1/z`),

which has **determinant `+1`** — orientation-preserving, the elliptic *rotation*: the two reflections
compose to a rotation, the classical fact, here reading "additive fold ∘ multiplicative fold = the
founding swap".  `S` is the order-4 elliptic generator (`S⁴ = I`) with `S² = −I`
(`ModularElliptic.modular_generator_orders`), so its **matrix order `4` halves to projective order
`2`** — exactly the order-halving the fixture sees (`bothSwap` is an involution).  The folds commute
only *projectively*: `R · N = −I · S` differs from `N · R = S` by the central `−I` (the Cassini sign),
which acts trivially on the projective line — so `{I, N, R, S}` is Klein four modulo `±I`, the matrix
witness of the fixture's `klein_four_group`.
-/

namespace E213.Lib.Math.Real213.FoldReflections

open E213.Lib.Math.Real213.ModularElliptic (Mat2 mul I2 negI2 S)

/-- Negation `z ↦ −z` as a matrix — the additive fold (a reflection, `det = −1`). -/
def N : Mat2 := ⟨-1, 0, 0, 1⟩

/-- Reciprocal `z ↦ 1/z` as a matrix — the multiplicative fold (a reflection, `det = −1`). -/
def R : Mat2 := ⟨0, 1, 1, 0⟩

/-! ## Both folds are reflections (involutions, `det = −1`) -/

theorem N_involutive : mul N N = I2 := by decide
theorem R_involutive : mul R R = I2 := by decide

theorem N_det : N.a * N.d - N.b * N.c = -1 := by decide
theorem R_det : R.a * R.d - R.b * R.c = -1 := by decide

/-- `S` is orientation-preserving (`det = +1`): the product of the two reflections is a rotation. -/
theorem S_det : S.a * S.d - S.b * S.c = 1 := by decide

/-! ## The product of the two folds is the founding swap -/

/-- ★★★ **`N · R = S`.**  Negation ∘ reciprocal (additive fold ∘ multiplicative fold) is the founding
    elliptic swap `S = z ↦ −1/z` — the matrix form of the fixture's antipode `bothSwap`. -/
theorem negation_recip_eq_swap : mul N R = S := by decide

/-- ★★ **The folds commute only projectively.**  `R · N = −I · S` differs from `N · R = S` by the
    central `−I` (the Cassini sign) — equal on the projective line, distinct as matrices. -/
theorem recip_negation_eq_neg_swap : mul R N = mul negI2 S := by decide

/-- ★★ **`S` central-squares.**  `S² = −I` — `S` has matrix order `4` but projective order `2`
    (`−I` acts trivially on the projective line), the order-halving the fixture's involution sees. -/
theorem S_sq_central : mul S S = negI2 := by decide

/-- ★★★★ **Two reflections compose to the founding rotation.**  The additive fold `N` and the
    multiplicative fold `R` are involutive reflections (`N² = R² = I`, `det = −1`); their product is
    the founding elliptic swap `S` (`det = +1`, orientation-preserving), which central-squares
    (`S² = −I`, matrix order `4` ≡ projective order `2`).  This is the matrix witness of
    `FoldKlein.klein_four_group`: `{I, N, R, S}` is Klein four modulo the central `±I`. -/
theorem two_reflections_compose_to_founding_swap :
    (mul N N = I2 ∧ mul R R = I2)
    ∧ (N.a * N.d - N.b * N.c = -1 ∧ R.a * R.d - R.b * R.c = -1 ∧ S.a * S.d - S.b * S.c = 1)
    ∧ mul N R = S
    ∧ mul S S = negI2 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Real213.FoldReflections
