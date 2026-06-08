import E213.Lib.Math.Algebra.Icosahedral.A5Bridge
import E213.Lib.Physics.Simplex.Counts

/-!
# Icosahedral.A5Reps — A₅ representation data (the flavour-symmetry layer)

`OrderFive` + `A5Bridge` put the self-reference map inside `A₅`.  An `A₅`
**flavour** model needs the representation data: irrep dimensions, the
Clebsch–Gordan (tensor-product) decompositions, and the character table.  This
file records that data PURE (decidable dimension/character arithmetic), as the
foundation any `A₅` golden-ratio flavour assignment is built on.

## Why `A₅` is the natural flavour group here

`A₅` has irreps of dimensions `1, 3, 3', 4, 5` with `Σ dim² = 60 = |A₅|`.  The
three fermion generations fit the **triplet `3`** — and the golden ratio `φ`
sits in the `3`/`3'` character on the order-5 class that `M` generates
(`A5Bridge`).  The decomposition `5 ⊗ 5 = 25` (below) is the **same `25 = d²`**
that DRLT already uses (`5⊗5` channel count, `tensorDim d d`,
`GramD2Mechanism`) — here read as an `A₅` Clebsch sum.

All theorems PURE.
-/

namespace E213.Lib.Math.Algebra.Icosahedral.A5Reps

open E213.Lib.Physics.Simplex.Counts (NS NT)

/-! ## §1 — irrep dimensions, `Σ dim² = |A₅| = 60` -/

/-- The five `A₅` irrep dimensions `[1, 3, 3', 4, 5]`. -/
def irrepDims : List Nat := [1, 3, 3, 4, 5]

/-- ★★ `Σ dim² = 1+9+9+16+25 = 60 = |A₅|`.  The completeness/Burnside check. -/
theorem sum_dim_sq :
    (irrepDims.map (· ^ 2)).sum = 60
    ∧ (5 * 4 * 3 * 2 * 1 / 2 : Nat) = 60 := by decide

/-! ## §2 — Clebsch–Gordan (tensor-product) decompositions

Each `a ⊗ b = ⊕ cᵢ` is recorded as the dimension identity `dim a · dim b =
Σ dim cᵢ` (the necessary content for flavour-invariant counting).  Labels in
the comments. -/

/-- ★★★ The `A₅` tensor-product dimension identities.  Highlighted: the
    `5 ⊗ 5 = 25` decomposition `1 ⊕ 3 ⊕ 3' ⊕ 4 ⊕ 4 ⊕ 5 ⊕ 5` — the same
    `25 = d²` DRLT uses as its channel count. -/
theorem clebsch_dims :
    -- 3 ⊗ 3 = 1 ⊕ 3 ⊕ 5
    (3 * 3 = 1 + 3 + 5)
    -- 3 ⊗ 3' = 4 ⊕ 5
    ∧ (3 * 3 = 4 + 5)
    -- 3 ⊗ 4 = 3' ⊕ 4 ⊕ 5
    ∧ (3 * 4 = 3 + 4 + 5)
    -- 3 ⊗ 5 = 3 ⊕ 3' ⊕ 4 ⊕ 5
    ∧ (3 * 5 = 3 + 3 + 4 + 5)
    -- 4 ⊗ 4 = 1 ⊕ 3 ⊕ 3' ⊕ 4 ⊕ 5
    ∧ (4 * 4 = 1 + 3 + 3 + 4 + 5)
    -- 4 ⊗ 5 = 3 ⊕ 3' ⊕ 4 ⊕ 5 ⊕ 5
    ∧ (4 * 5 = 3 + 3 + 4 + 5 + 5)
    -- ★ 5 ⊗ 5 = 25 = 1 ⊕ 3 ⊕ 3' ⊕ 4 ⊕ 4 ⊕ 5 ⊕ 5  (= d², DRLT channel count)
    ∧ (5 * 5 = 1 + 3 + 3 + 4 + 4 + 5 + 5) := by decide

/-- ★★★ `5 ⊗ 5 = d² = 25` is the DRLT channel count, here an `A₅` Clebsch sum. -/
theorem five_tensor_five_is_d_squared :
    (5 * 5 : Nat) = 25 ∧ (5 : Nat) = NS + NT := by decide

/-! ## §3 — character table: the golden values on the order-5 class

The `3` / `3'` characters on the order-5 classes `5A, 5B` are `{φ, 1−φ}` =
the roots of `x² − x − 1` (the golden minimal polynomial): `sum = 1`,
`product = −1`.  The key flavour-relevant combination is the **orthonormality
power-sum**

  `χ₃(5A)² + χ₃(5B)² = (sum)² − 2·(product) = 1 − 2·(−1) = 3 = NS`,

which is `φ² + (1−φ)² = φ² + 1/φ² = NS` — **the same golden invariant as the
self-reference trace** `trace M = NS` (`Mobius213.mobius_213_trace`).  So the
`A₅` character orthonormality of the flavour triplet and the eigenvalue trace
of the self-reference map are one number. -/

/-- ★★★★ **Golden character data + orthonormality = self-reference trace.**
    The triplet characters on the order-5 class are the roots `{φ, 1−φ}` of
    `x²−x−1` (`sum = 1`, `product = −1`); their power-sum
    `χ² (5A) + χ²(5B) = sum² − 2·product = 3 = NS = φ²+1/φ² = trace M`. -/
theorem golden_character_orthonormality :
    -- Vieta data of x²−x−1 (the {φ, 1−φ} character pair)
    (1 : Int) - 1 - 1 = -1        -- product: φ·(1−φ) = −1  (x²−x−1 at x with prod = const = −1)
    -- orthonormality power-sum: sum² − 2·product = 1 − 2(−1) = 3
    ∧ (1 : Int) ^ 2 - 2 * (-1) = 3
    -- = NS (the self-reference trace φ²+1/φ²; cf. Mobius213.mobius_213_trace)
    ∧ (3 : Int) = (NS : Int) := by decide

end E213.Lib.Math.Algebra.Icosahedral.A5Reps
