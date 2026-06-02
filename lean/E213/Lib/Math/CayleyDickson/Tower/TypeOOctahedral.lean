import E213.Lib.Math.CayleyDickson.Integer.Hurwitz213
import E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian

/-!
# The octahedral order over `ℤ[√2]`, and its order-8 unit

The binary polyhedral groups complete the exceptional `E₆–E₇–E₈` rungs of
the McKay correspondence as unit groups of definite quaternion orders:

| group | order | base ring | new torsion | McKay |
|---|---|---|---|---|
| `2T` (binary tetrahedral) | 24 | `ℤ` (Hurwitz) | `3,6` | `E₆` |
| `2O` (binary octahedral) | 48 | `ℤ[√2]` | `8` | `E₇` |
| `2I` (binary icosahedral) | 120 | `ℤ[φ]` = `ℤ[√5]` | `5,10` | `E₈` |

`2T` lives over `ℤ`; `2O` and `2I` over the *real* quadratic rings
`ℤ[√2]`, `ℤ[√5]`, whose own unit groups are infinite (real quadratic)
while the totally-definite quaternion orders over them have finite unit
groups (`2O`, `2I`).  This file is the `√2` companion of `TypeEIcosian`
(the `√5`/`φ` case): it constructs `ℤ[√2]` and the `ℤ[√2]`-coordinate
quaternions (scaled-by-2, Hurwitz convention) and exhibits an explicit
**order-8 unit** — the octahedral `(1+i)/√2 = cos 45° + sin 45°·i`,
whose order-8 torsion is the `E₇` signature, carried by neither `2T`
(orders `⊆ {1,2,3,4,6}`) nor `2I` (orders `⊆ {1,2,3,4,5,6,10}`).
-/

namespace E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral

/-- Real golden... no: `ℤ[√2]`, `⟨a,b⟩ = a + b√2`, with `(√2)² = 2`. -/
structure ZRt2 where
  a : Int
  b : Int
deriving DecidableEq

namespace ZRt2

/-- `(a+b√2)(c+d√2) = (ac+2bd) + (ad+bc)√2`. -/
def mul (x y : ZRt2) : ZRt2 :=
  ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩

instance : Mul ZRt2 := ⟨mul⟩
instance : Add ZRt2 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg ZRt2 := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub ZRt2 := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩

/-- Coordinatewise halving — exact on octahedral unit products. -/
def half (x : ZRt2) : ZRt2 := ⟨x.a / 2, x.b / 2⟩

end ZRt2

/-- Octahedral quaternion: four `ℤ[√2]` coordinates, scaled by 2
    (Hurwitz convention with `ℤ[√2]` for `ℤ`). -/
structure Octahedral where
  q0 : ZRt2
  q1 : ZRt2
  q2 : ZRt2
  q3 : ZRt2
deriving DecidableEq

namespace Octahedral

/-- Quaternion multiplication over `ℤ[√2]`, halved (scaled-by-2). -/
def mul (u v : Octahedral) : Octahedral :=
  ⟨ZRt2.half (u.q0 * v.q0 - u.q1 * v.q1 - u.q2 * v.q2 - u.q3 * v.q3),
   ZRt2.half (u.q0 * v.q1 + u.q1 * v.q0 + u.q2 * v.q3 - u.q3 * v.q2),
   ZRt2.half (u.q0 * v.q2 - u.q1 * v.q3 + u.q2 * v.q0 + u.q3 * v.q1),
   ZRt2.half (u.q0 * v.q3 + u.q1 * v.q2 - u.q2 * v.q1 + u.q3 * v.q0)⟩

instance : Mul Octahedral := ⟨mul⟩

/-- The identity `1`, scaled by 2. -/
def one : Octahedral := ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Reduced norm `q₀²+q₁²+q₂²+q₃²` in `ℤ[√2]` (= `4` for a scaled unit). -/
def normSq (u : Octahedral) : ZRt2 :=
  u.q0 * u.q0 + u.q1 * u.q1 + u.q2 * u.q2 + u.q3 * u.q3

end Octahedral

/-- An order-8 octahedral unit: `g = (1 + i)/√2 = cos 45° + sin 45°·i`,
    scaled to `⟨√2, √2, 0, 0⟩ = ⟨⟨0,1⟩, ⟨0,1⟩, ⟨0,0⟩, ⟨0,0⟩⟩`.  Real part
    `√2/2 = cos 45°`, norm `1`; `g² = i`, `g⁴ = -1`, `g⁸ = 1`. -/
def g8 : Octahedral := ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- ★ **An explicit order-8 unit of the octahedral quaternion order.**  `g`
    is a unit (`normSq g = 4`, halving-free witness `|g| = 1`),
    `g⁸ = 1` while `g⁴ ≠ 1` — so its order divides 8 but not 4, hence is
    exactly 8.  `g` is one of the 48 unit octahedrals (the binary
    octahedral group `2O`, a cited classical fact); its order-8 torsion is
    the `E₇` signature, carried by neither `2T` nor `2I`.  Only the
    explicit element is proved here, not the full `2O` group. -/
theorem octahedral_order8_unit :
    Octahedral.normSq g8 = ⟨4, 0⟩
    ∧ g8 * g8 * g8 * g8 * g8 * g8 * g8 * g8 = Octahedral.one
    ∧ g8 * g8 * g8 * g8 ≠ Octahedral.one := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

open E213.Lib.Math.CayleyDickson.Integer.Hurwitz213 in
/-- ★ **`2T` has no order-8 element.**  Every Hurwitz unit has order in
    `{1,2,3,4,6}` (`hur_orderOf` returns `0` for any order outside that
    menu — including 8 — and `hur_order_distribution` proves that `0`-count
    is `0`).  So the order-8 octahedral torsion is genuinely new at the
    `E₇` rung, not present at `E₆`. -/
theorem two_T_has_no_order_8 :
    hur_units.countP (fun u => hur_orderOf u = 0) = 0 :=
  hur_order_distribution.2.2.2.2.2

end E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral
