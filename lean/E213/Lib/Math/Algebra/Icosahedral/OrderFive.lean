import E213.Lib.Math.Algebra.Mobius213
import E213.Lib.Physics.Simplex.Counts

/-!
# Icosahedral.OrderFive — the self-reference map is an order-5 element of A₅

`Mobius213ModFive` proves `P⁵ ≡ −I (mod 5)` and `P¹⁰ ≡ +I (mod 5)` at the
matrix-entry level (from the precomputed Pell entries `89, 55, 34`). This file
closes the **group-theoretic** gap that the entry-level statement leaves open:
the *order* is **exactly** 10 in `SL(2,𝔽₅)` (and **exactly** 5 in
`PSL(2,𝔽₅) ≅ A₅`), i.e. no smaller power returns to `±I`.

It does this by computing the **whole mod-5 orbit** with genuine `𝔽₅`-matrix
multiplication (not precomputed integer entries), so `decide` verifies every
intermediate power directly.

## Why this matters (the bridge)

**Repo cross-reference**: `Algebra/CayleyDickson/Tower/MobiusPIcosian.lean`
already proves `P mod 5` has order exactly `10` in `SL(2,𝔽₅) ≅ 2I` (the binary
icosahedral group, `E₈` McKay rung, icosian units over `ℤ[φ]`) via the
`pellCoeff` Cayley–Hamilton detector.  This file is complementary: it computes
the **explicit `𝔽₅`-matrix orbit** and reads off the **`PSL`/`A₅` order-5**
(the rotation group, `2I/{±1}`), used by the flavour layer here.

`PSL(2,5) ≅ A₅ ≅` the **icosahedral rotation group** (Groupprops; standard).
An order-5 element of `A₅` is a **5-fold rotation axis** of the icosahedron —
the conjugacy class `C₅` whose character, in the standard 3-dim irrep, is the
**golden ratio** `φ` (next file, `A5Bridge`). So the §5.6 self-reference map
`M = [[c,1],[1,1]]`, reduced mod `d = 5`, **is** such a 5-fold icosahedral
rotation. This is the same `M` whose ℝ-eigenvalue is `φ²` (`Mobius213`): one
matrix, two Lens readings — frozen ℝ-eigenvalue `φ²`, and mod-`d` group element
of `A₅` carrying character `φ`. `d = 5` plays a **double role**:
`disc M = NS²−4 = d` (ℝ side) AND `𝔽₅` is the field realising `A₅` (mod side).

All theorems PURE (`decide` on 𝔽₅-matrix arithmetic).
-/

namespace E213.Lib.Math.Algebra.Icosahedral.OrderFive

/-! ## §1 — 𝔽₅ 2×2 matrices as Nat 4-tuples `(a,b,c,d)` for `[[a,b],[c,d]]` -/

/-- A 2×2 matrix over `𝔽₅`, entries reduced mod 5. -/
abbrev Mat5 := Nat × Nat × Nat × Nat

/-- `𝔽₅` matrix product (entries kept in `0..4`). -/
def mul5 : Mat5 → Mat5 → Mat5
  | (a, b, c, d), (e, f, g, h) =>
    ((a * e + b * g) % 5, (a * f + b * h) % 5,
     (c * e + d * g) % 5, (c * f + d * h) % 5)

/-- Identity `I`. -/
def I  : Mat5 := (1, 0, 0, 1)
/-- The central element `−I = [[4,0],[0,4]]` (`4 ≡ −1 mod 5`). -/
def negI : Mat5 := (4, 0, 0, 4)
/-- The self-reference map `M = [[c,1],[1,1]] = [[2,1],[1,1]]` reduced mod 5. -/
def M  : Mat5 := (2, 1, 1, 1)

/-- `M^n` by left-multiplication, mod 5 throughout. -/
def pow : Nat → Mat5
  | 0     => I
  | n + 1 => mul5 (pow n) M

/-! ## §2 — the full mod-5 orbit (genuine 𝔽₅ multiplication)

Each power is computed by `mul5`, so these equalities verify the matrix
arithmetic itself — not precomputed Pell entries. -/

/-- ★★ The complete order-10 orbit of `M` in `SL(2,𝔽₅)`. -/
theorem orbit :
    pow 1 = (2, 1, 1, 1)
    ∧ pow 2 = (0, 3, 3, 2)
    ∧ pow 3 = (3, 3, 3, 0)
    ∧ pow 4 = (4, 1, 1, 3)
    ∧ pow 5 = (4, 0, 0, 4)   -- = −I
    ∧ pow 6 = (3, 4, 4, 4)
    ∧ pow 7 = (0, 2, 2, 3)
    ∧ pow 8 = (2, 2, 2, 0)
    ∧ pow 9 = (1, 4, 4, 2)
    ∧ pow 10 = (1, 0, 0, 1) := by decide   -- = I

/-! ## §3 — order EXACTLY 5 in `PSL(2,𝔽₅) ≅ A₅`

`Mobius213ModFive` shows `pow 5 = −I` and `pow 10 = I`.  The *exactness* — that
no smaller power lands in the centre `{I, −I}` — is what makes the image a
**genuine order-5** element (a 5-fold icosahedral rotation, not a lower-order
one).  In `PSL` the centre `{I, −I}` is quotiented to the identity, so the
image of `M` has order `5`. -/

/-- ★★★ **Order exactly 10 in `SL(2,𝔽₅)`**: `pow k ≠ I` for `1 ≤ k ≤ 9`, and
    `pow 10 = I`.  No early return to the identity. -/
theorem order_exactly_ten :
    pow 1 ≠ I ∧ pow 2 ≠ I ∧ pow 3 ≠ I ∧ pow 4 ≠ I ∧ pow 5 ≠ I
    ∧ pow 6 ≠ I ∧ pow 7 ≠ I ∧ pow 8 ≠ I ∧ pow 9 ≠ I ∧ pow 10 = I := by decide

/-- ★★★★ **Order exactly 5 in `PSL(2,𝔽₅) ≅ A₅`**: the image of `M` avoids the
    centre `{I, −I}` for `1 ≤ k ≤ 4`, and hits `−I` (central ≡ identity in PSL)
    exactly at `k = 5`.  Hence `M` is an **order-5** element of `A₅` — a 5-fold
    icosahedral rotation. -/
theorem order_exactly_five_in_psl :
    (pow 1 ≠ I ∧ pow 1 ≠ negI)
    ∧ (pow 2 ≠ I ∧ pow 2 ≠ negI)
    ∧ (pow 3 ≠ I ∧ pow 3 ≠ negI)
    ∧ (pow 4 ≠ I ∧ pow 4 ≠ negI)
    ∧ pow 5 = negI := by decide

/-! ## §4 — `d = 5` is the field, `disc M = d` is the ℝ shadow -/

/-- ★★★ **`d = 5` double role.**  The reduction modulus is `d = NS + NT = 5`,
    the same `d` that is the ℝ-side discriminant `disc M = NS²−4 = 5`
    (`Mobius213.mobius_213_discriminant`).  So the field `𝔽_d = 𝔽₅` realising
    `PSL(2,d) ≅ A₅` and the discriminant that gives `M` its golden eigenvalues
    are the **same atomic `d`**. -/
theorem d_double_role :
    -- reduction modulus = d = NS + NT
    (5 : Nat) = E213.Lib.Physics.Simplex.Counts.NS + E213.Lib.Physics.Simplex.Counts.NT
    -- ℝ-side: disc M = NS² − 4 = 5 = d  (Int form, cf. Mobius213)
    ∧ (3 : Int) ^ 2 - 4 * 1 = 5 := by decide

/-- The `𝔽₅` determinant `ad − bc` (the `+25` keeps the `Nat` subtraction
    non-truncating before reducing mod 5; entries `≤ 4` ⟹ `bc ≤ 16 < 25`). -/
def det5 : Mat5 → Nat
  | (a, b, c, d) => (a * d + 25 - b * c) % 5

/-- ★★ **The icosahedral order-10 orbit lies in `SL(2,𝔽₅)`** — `det = 1` is
    preserved along the *entire* orbit of `M`, not merely `M ∈ GL`.  The
    determinant invariant complementing `orbit` (entries) and `order_exactly_ten`
    (period): the order-5 (in `PSL`) icosahedral rotation is a *special*-linear map. -/
theorem orbit_in_SL :
    det5 (pow 1) = 1 ∧ det5 (pow 2) = 1 ∧ det5 (pow 3) = 1 ∧ det5 (pow 4) = 1
    ∧ det5 (pow 5) = 1 ∧ det5 (pow 6) = 1 ∧ det5 (pow 7) = 1 ∧ det5 (pow 8) = 1
    ∧ det5 (pow 9) = 1 ∧ det5 (pow 10) = 1 := by decide

/-- ★ **`M⁵ = −I` is the central involution** — the non-trivial element of the
    centre `{I, −I} ≅ ℤ/2` of the order-10 group: `M⁵ ≠ I` yet `(M⁵)² = I`.  The
    `PSL`-quotient kernel made explicit (what `order_exactly_ten` implies but does
    not record as an involution law). -/
theorem pow_five_order_two : pow 5 ≠ I ∧ mul5 (pow 5) (pow 5) = I := by decide

end E213.Lib.Math.Algebra.Icosahedral.OrderFive
