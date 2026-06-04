import E213.Lib.Physics.Simplex.Counts

/-!
# The three axes over `ℕ`: integer companion matrices, surd-free

`NaturalTowerForm` (`Phase 26`) showed the `E₈` seed `√5` dissolves, over
`ℕ`, into the Lucas recurrence `= trace Pⁿ`.  This file completes the
trichotomy: **all three axes are pure integer companion matrices**, their
seeds the eigenvalue shadows, surd-free.

Each axis `√D` is the fundamental object of a quadratic order, and over
`ℕ` it is the recurrence (companion matrix) of its minimal polynomial:

| axis  | matrix `M`        | min poly       | `trace Mⁿ`       | disc           | type            |
|-------|-------------------|----------------|------------------|----------------|-----------------|
| `2`   | `[[NT,1],[1,0]]`  | `x²−NT·x−1`    | `2,2,6,14,34,…`  | `NT²+4 = 8`    | real (Pell)     |
| `3`   | `[[0,−1],[1,−1]]` | `x²+x+1` (`Φ₃`)| `2,−1,−1` (per 3)| `1−4 = −NS`    | imaginary (cyc) |
| `2+3` | `[[2,1],[1,1]]=P` | `x²−NS·x+1`   | `2,3,7,18,47,…`  | `NS²−4 = NS+NT`| real (Lucas)    |

The **discriminant sign** is the field type, hence the dynamics:

  * `disc > 0` (`8, 5`) — *real* quadratic ⇒ unit group infinite ⇒ the
    trace **grows** (`Pell`, `Lucas`); the `2`- and `2+3`-axes.
  * `disc < 0` (`−NS = −3`) — *imaginary* quadratic ⇒ unit group finite ⇒
    the trace is **periodic** (`Mₐ³ = I`, order `NS`); the `3`-axis
    (`Eisenstein ω`).

So over `ℕ` there are no surds at all: three integer matrices, two
hyperbolic (real, growing) and one elliptic-periodic (imaginary, order
`NS`).  The `√D = √8/2, √5, √−3` are exactly the `ℝ`-eigenvalues
(`1±√2`, `φ²,φ⁻²`, `ω,ω̄`) — the diagonalisation shadows.  The
discriminants `{8, −NS, NS+NT} = {8, −3, 5}` are the field discriminants
(`Phase 19/23`); the recurrence coefficients are the atomic `{NT, NS}`.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.ThreeAxisRecurrence

open E213.Lib.Physics.Simplex.Counts

/-- Integer `2×2` matrix as `(a,b,c,d) = [[a,b],[c,d]]`. -/
abbrev Mat := Int × Int × Int × Int

def mm (x y : Mat) : Mat :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
   x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)
def I2 : Mat := (1, 0, 0, 1)
def matPow (A : Mat) : Nat → Mat
  | 0     => I2
  | n + 1 => mm (matPow A n) A
def tr (A : Mat) : Int := A.1 + A.2.2.2

/-- The three axis companion matrices. -/
def M2 : Mat := (2, 1, 1, 0)   -- ℤ[√2], x² − NT·x − 1
def M3 : Mat := (0, -1, 1, -1)  -- ℤ[ω],  x² + x + 1 = Φ₃
def Pm : Mat := (2, 1, 1, 1)   -- ℤ[φ],  x² − NS·x + 1

/-- **`2`-axis — `ℤ[√2]`, the Pell recurrence.**  `trace M₂ⁿ =
    2,2,6,14,34` (coefficient `NT`, `a_{n+1}=NT·a_n+a_{n−1}`); disc
    `NT²+4 = 8 > 0` (real, growing).  `√2 = ` eigenvalue shadow
    (`1±√2`). -/
theorem axis_two_pell :
    (tr (matPow M2 0), tr (matPow M2 1), tr (matPow M2 2), tr (matPow M2 3),
      tr (matPow M2 4)) = (2, 2, 6, 14, 34)
    ∧ ((NT : Int) * NT + 4 = 8) := by decide

/-- **`3`-axis — `ℤ[ω]`, the cyclotomic `Φ₃`.**  `trace M₃ⁿ = 2,−1,−1`
    (period `3`), and `M₃³ = I` (finite, order `NS`); disc `1−4 = −NS < 0`
    (imaginary, periodic).  `ω = ` eigenvalue shadow. -/
theorem axis_three_eisenstein :
    (tr (matPow M3 0), tr (matPow M3 1), tr (matPow M3 2), tr (matPow M3 3))
        = (2, -1, -1, 2)
    ∧ (matPow M3 3 = I2)                       -- order NS = 3
    ∧ ((1 : Int) * 1 - 4 * 1 = -(NS : Int)) := by decide

/-- **`2+3` axis — `ℤ[φ]`, the Lucas recurrence.**  `trace Pⁿ =
    2,3,7,18,47` (coefficient `NS`, `a_{n+1}=NS·a_n−a_{n−1}`); disc
    `NS²−4 = NS+NT = 5 > 0` (real, growing).  `φ²,φ⁻² = ` eigenvalue
    shadow. -/
theorem axis_two_three_lucas :
    (tr (matPow Pm 1), tr (matPow Pm 2), tr (matPow Pm 3), tr (matPow Pm 4))
        = (3, 7, 18, 47)
    ∧ ((NS : Int) * NS - 4 = (NS : Int) + NT) := by decide

/-- **The discriminant sign is the field type.**  `disc ∈ {8, NS+NT} > 0`
    (real, growing) for the `2`- and `2+3`-axes; `disc = −NS < 0`
    (imaginary, periodic/finite) for the `3`-axis. -/
theorem disc_sign_is_field_type :
    -- real (positive disc): grows.
    ((NT : Int) * NT + 4 = 8 ∧ (0 : Int) < 8)
    ∧ ((NS : Int) * NS - 4 = (NS : Int) + NT ∧ (0 : Int) < (NS : Int) + NT)
    -- imaginary (negative disc): periodic, finite order NS.
    ∧ ((1 : Int) * 1 - 4 * 1 = -(NS : Int) ∧ -(NS : Int) < 0 ∧ matPow M3 3 = I2) := by
  decide

/-- ★★★ **The three axes over `ℕ` are surd-free integer matrices.**  Each
    seed `√D` is the eigenvalue shadow of an integer companion matrix:
    `2`-axis `ℤ[√2]` (Pell, `trace 2,2,6,14,34`, disc `8`), `3`-axis
    `ℤ[ω]` (cyclotomic `Φ₃`, period `3`, `M³=I`, disc `−NS`), `2+3`-axis
    `ℤ[φ]` (Lucas, `trace 2,3,7,18,47`, disc `NS+NT`).  Discriminant sign
    = field type: `>0` real/growing, `<0` imaginary/periodic.  No surds —
    just three integer matrices with atomic coefficients `{NT, NS}`. -/
theorem three_axes_surd_free :
    -- 2-axis: Pell, growing, disc 8.
    ((tr (matPow M2 2), tr (matPow M2 3)) = (6, 14) ∧ (NT : Int) * NT + 4 = 8)
    -- 3-axis: cyclotomic, periodic, M³=I (order NS), disc −NS.
    ∧ (matPow M3 3 = I2 ∧ (1 : Int) * 1 - 4 * 1 = -(NS : Int))
    -- 2+3: Lucas, growing, disc NS+NT.
    ∧ ((tr (matPow Pm 2), tr (matPow Pm 3)) = (7, 18)
        ∧ (NS : Int) * NS - 4 = (NS : Int) + NT) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Algebra.CayleyDickson.Tower.ThreeAxisRecurrence
