/-!
# Type E seed — the icosian order over `ℤ[φ]`, and its order-5 unit

The seed ladder of the meta-Cayley–Dickson tower runs through the finite
unit groups of definite arithmetic orders: the rank-1 imaginary quadratic
seeds (`μ₂, μ₄, μ₆` for `ℤ[√-2], ℤ[i], ℤ[ω]`) and the rank-2 quaternion
seed Hurwitz (`2T`, 24 units).  The **next rung is the icosian order** —
the maximal order of the definite quaternion algebra `(-1,-1)` over
`ℚ(√5)`, whose unit group is the **binary icosahedral group
`2I ≅ SL(2,𝔽₅)` of order 120**.

Two number-theoretic facts frame this:
  * `ℚ(√5)` is a *real* quadratic field, so `ℤ[φ]` itself has an
    *infinite* unit group (`φ` is a fundamental unit) — which is exactly
    why the strict `ℤ`-coefficient Cayley–Dickson matrix excludes the
    icosian as a "Type E" seed (`Misc/TypeE_Rejection`).
  * but the *quaternion order* over `ℤ[φ]` is *totally definite*, so its
    unit group is *finite*: `2I`, order 120.  That is the relevant object
    for the binary-polyhedral / McKay continuation past `2T`.

`2I`'s element orders are `{1,2,3,4,5,6,10}` — so it carries **order-5
(and order-10) torsion absent from every lower seed** (whose menus stop
at 6).  This file constructs `ℤ[φ]` and the `ℤ[φ]`-coordinate quaternions
(scaled-by-2, exactly as Hurwitz over `ℤ`), and exhibits an explicit
**order-5 icosian unit** — the executable witness of the golden /
pentagonal branch, which the repo previously only named textually
(`SL(2,𝔽₅) ≅ 2I`).
-/

namespace E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian

/-- Golden integers `ℤ[φ]`: `⟨a,b⟩ = a + b·φ`, with `φ² = φ + 1`. -/
structure ZPhi where
  a : Int
  b : Int
deriving DecidableEq

namespace ZPhi

/-- `(a+bφ)(c+dφ) = (ac+bd) + (ad+bc+bd)φ` (using `φ² = φ+1`). -/
def mul (x y : ZPhi) : ZPhi :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Mul ZPhi := ⟨mul⟩
instance : Add ZPhi := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg ZPhi := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub ZPhi := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩

/-- Coordinatewise halving — exact on icosian unit products (which land
    in the `2·`lattice, as for Hurwitz over `ℤ`). -/
def half (x : ZPhi) : ZPhi := ⟨x.a / 2, x.b / 2⟩

end ZPhi

/-- Icosian quaternion: four `ℤ[φ]` coordinates, scaled by 2 (so a unit
    `(q₀+q₁i+q₂j+q₃k)/2` is stored as `⟨q₀,q₁,q₂,q₃⟩`), exactly the
    Hurwitz convention with `ℤ[φ]` replacing `ℤ`. -/
structure Icosian where
  q0 : ZPhi
  q1 : ZPhi
  q2 : ZPhi
  q3 : ZPhi
deriving DecidableEq

namespace Icosian

/-- Quaternion multiplication over `ℤ[φ]`, halved (scaled-by-2). -/
def mul (u v : Icosian) : Icosian :=
  ⟨ZPhi.half (u.q0 * v.q0 - u.q1 * v.q1 - u.q2 * v.q2 - u.q3 * v.q3),
   ZPhi.half (u.q0 * v.q1 + u.q1 * v.q0 + u.q2 * v.q3 - u.q3 * v.q2),
   ZPhi.half (u.q0 * v.q2 - u.q1 * v.q3 + u.q2 * v.q0 + u.q3 * v.q1),
   ZPhi.half (u.q0 * v.q3 + u.q1 * v.q2 - u.q2 * v.q1 + u.q3 * v.q0)⟩

instance : Mul Icosian := ⟨mul⟩

/-- The identity `1`, scaled by 2. -/
def one : Icosian := ⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Reduced norm `q₀²+q₁²+q₂²+q₃²` in `ℤ[φ]` (= `4` for a scaled unit). -/
def normSq (u : Icosian) : ZPhi :=
  u.q0 * u.q0 + u.q1 * u.q1 + u.q2 * u.q2 + u.q3 * u.q3

end Icosian

/-- An order-5 icosian unit: `g = ((φ-1) + φ·i + j)/2`, scaled to
    `⟨φ-1, φ, 1, 0⟩ = ⟨⟨-1,1⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨0,0⟩⟩`.  Real part
    `(φ-1)/2 = cos 72°`, norm `1`. -/
def g5 : Icosian := ⟨⟨-1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩

/-- ★ **An explicit order-5 unit of the icosian order (`2I`).**  `g`
    is a unit (`normSq g = 4`, i.e. `|g| = 1` in the scaled rep), `g⁵ = 1`,
    and `g ≠ 1` — so (since 5 is prime) `g` has order exactly 5.  This is
    the order-5 torsion that the binary-icosahedral seed `2I` carries and
    no lower seed (`μ₂,μ₄,μ₆,2T`, menus `⊆ {1,2,3,4,6}`) does — the golden
    / pentagonal McKay branch, here over `ℤ[φ]`. -/
theorem icosian_order5_unit :
    Icosian.normSq g5 = ⟨4, 0⟩
    ∧ g5 * g5 * g5 * g5 * g5 = Icosian.one
    ∧ g5 ≠ Icosian.one := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- An order-10 icosian unit: `g₁₀ = (φ + i + (φ-1)·j)/2`, scaled
    `⟨φ, 1, φ-1, 0⟩`.  Real part `φ/2 = cos 36°`, norm `1`. -/
def g10 : Icosian := ⟨⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩⟩

set_option maxHeartbeats 1000000 in
/-- ★ **An explicit order-10 unit of the icosian order (`2I`).**  `g₁₀`
    is a unit (`normSq = 4`), `g₁₀¹⁰ = 1`, while `g₁₀⁵ ≠ 1` and
    `g₁₀² ≠ 1` — so its order divides 10 but neither 5 nor 2, hence is
    exactly 10.  With `g5`, this exhibits `2I`'s full new torsion menu
    `{5, 10}` — the pentagonal orders absent from every lower seed
    (`μ₂,μ₄,μ₆,2T`, orders `⊆ {1,2,3,4,6}`). -/
theorem icosian_order10_unit :
    Icosian.normSq g10 = ⟨4, 0⟩
    ∧ g10 * g10 * g10 * g10 * g10 * g10 * g10 * g10 * g10 * g10 = Icosian.one
    ∧ g10 * g10 * g10 * g10 * g10 ≠ Icosian.one
    ∧ g10 * g10 ≠ Icosian.one := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian
