import E213.Lib.Physics.Simplex.Counts

/-!
# ModularElliptic — `PSL(2,ℤ) = ℤ₂ * ℤ₃`, and its elliptic orders `4, 6` are the axis

The modular group is the free product `PSL(2,ℤ) ≅ ℤ/2 * ℤ/3` (classical).  Its two elliptic
generators are `S : z ↦ −1/z` (fixing `i`, order 2 in `PSL`) and `U = ST` (fixing `ω`, order
3 in `PSL`).  In `SL(2,ℤ)` they have orders **4** and **6**, with `−I` the central
involution:

```
S = [[0,−1],[1,0]]   S² = −I   S⁴ = I    (order 4 = |ℤ[i]^×|, the Gaussian 2-point)
U = [[0,−1],[1,1]]   U³ = −I   U⁶ = I    (order 6 = |ℤ[ω]^×|, the Eisenstein 3-point)
```

So the modular group's elliptic structure is *exactly* the spiral axis: orders `{4, 6}` are
the Gaussian/Eisenstein unit-group orders (`ZIUnits`, `ZOmegaUnits`), `−I` is the central
`2` (the Cassini sign), and modulo it the point orders are `{2, 3}` whose `lcm = 6` is the
Eisenstein/π rotation period (`EisensteinCompletion.eisenstein_floor_rotation`,
`DepthPiQuartic`).  This is the `213`-native reading of `ℤ₂ * ℤ₃ = PSL(2,ℤ)`:

  - the **`S`-point** (order 4, `i`, disc `−4`) — the square/Gaussian axis;
  - the **`U`-point** (order 6, `ω`, disc `−3`) — the hexagonal/Eisenstein axis, the
    "circle" (elliptic, `M³ = −I`, periodic);
  - the binary cover `{4, 6} = 2·{2, 3}` matches `axis_binary_cover` and the crystallographic
    restriction `{1,2,3,4,6}`.
-/

namespace E213.Lib.Math.Real213.ModularElliptic

/-- Integer `2×2` matrices. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq

/-- Matrix product. -/
def mul (M N : Mat2) : Mat2 :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

def I2 : Mat2 := ⟨1, 0, 0, 1⟩
def negI2 : Mat2 := ⟨-1, 0, 0, -1⟩

/-- `S = [[0,−1],[1,0]]` — the order-4 elliptic generator (fixes `i`). -/
def S : Mat2 := ⟨0, -1, 1, 0⟩

/-- `U = [[0,−1],[1,1]]` — the order-6 elliptic generator (fixes `ω`). -/
def U : Mat2 := ⟨0, -1, 1, 1⟩

/-- ★★★★ **The modular elliptic orders are `4` and `6`.**  `S² = −I`, `S⁴ = I` (order 4 =
    `|ℤ[i]^×|`); `U³ = −I`, `U⁶ = I` (order 6 = `|ℤ[ω]^×|`).  These are the orders of the two
    elliptic generators of `SL(2,ℤ)`; modulo the central `−I` they have orders `2, 3`, the
    free factors of `PSL(2,ℤ) = ℤ₂ * ℤ₃`.  The `213`-native content of the table's middle
    row: the `{4,6}` axis (Gaussian/Eisenstein), with `−I` the central Cassini `2`. -/
theorem modular_generator_orders :
    mul S S = negI2
    ∧ mul (mul (mul S S) S) S = I2
    ∧ mul (mul U U) U = negI2
    ∧ mul (mul (mul (mul (mul U U) U) U) U) U = I2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The determinants are `1`: `S, U ∈ SL(2,ℤ)`. -/
theorem modular_generators_in_SL2 :
    S.a * S.d - S.b * S.c = 1 ∧ U.a * U.d - U.b * U.c = 1 := by decide

end E213.Lib.Math.Real213.ModularElliptic
