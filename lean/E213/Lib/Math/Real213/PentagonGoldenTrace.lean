/-!
# The pentagon trace is the golden conjugate — φ on the forbidden 5-fold axis

`ImaginaryQuadraticUnitTrichotomy.crystallographic_cosines` shows the *allowed* rotation orders
`{1,2,3,4,6}` have **integer** traces `2cos(2πk/6) ∈ {2,1,−1,−2}` (Eisenstein `ℤ[ω]`).  The
**forbidden** orders `5, 10` (the quasicrystal axis, excluded by
`Tower/CyclotomicTraceDegree.crystallographic_restriction`) are precisely where the *golden*
trace lives:

  * `2cos(π/5)  = (1+√5)/2 = φ`            — the decagon (10-fold) trace,
  * `2cos(2π/5) = (√5−1)/2 = φ − 1 = 1/φ`  — the pentagon (5-fold) trace.

Neither is an integer; both are **golden integers** `ℤ[φ] = ℤ[(1+√5)/2]`.  This file builds
`ℤ[φ]` and proves the algebraic skeleton of those two trigonometric identities — the part the
framework certifies ∅-axiom (the trigonometric value itself needs reals; the *algebraic
relations* the value satisfies are pure):

  * `phi_quad`            — `φ² = φ + 1` (the residue's self-reference quadratic, `Mobius213`).
  * `pentagon_trace_quad` — `(φ−1)² + (φ−1) = 1`: the pentagon trace `2cos(2π/5)` is the root
    of `x²+x−1`, the *conjugate* golden quadratic.
  * `pentagon_trace_unit` — `φ·(φ−1) = 1`: the pentagon trace is exactly `1/φ`.

## Why this anchors the φ↔π bridge

φ and π are not algebraically related (φ is degree 2, π transcendental), so any bridge between
them is through a **continuous Lens** — and the cosine (the trace of a rotation) is exactly
that Lens.  `φ = 2cos(π/5)` says: *the golden ratio is what the continuous-rotation Lens reads
on the forbidden 5-fold axis.*  Inverting, `π = 5·arccos(φ/2)` (the arc-length Lens of the
algebraic point `φ/2`).  This file pins the **algebraic value** the rotation Lens produces — φ
and its reciprocal `1/φ` — leaving the angle (`π/5`, transcendental) as the irreducibly
continuous part.  So π is the residue's continuous-symmetry image whose *value* the rotation
Lens cannot reach without the transcendental angle, while φ (the fixed-point image) *is*
reached, ∅-axiom, here.

All ∅-axiom.
-/

namespace E213.Lib.Math.Real213.PentagonGoldenTrace

/-- A **golden integer** `a + b·φ` in `ℤ[φ] = ℤ[(1+√5)/2]`, with `φ² = φ + 1`. -/
structure GoldenInt where
  a : Int
  b : Int
deriving DecidableEq

namespace GoldenInt

/-- Multiplication using `φ² = φ + 1`:
    `(a+bφ)(c+dφ) = (ac+bd) + (ad+bc+bd)φ`. -/
def mul (x y : GoldenInt) : GoldenInt :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

/-- Componentwise addition. -/
def add (x y : GoldenInt) : GoldenInt := ⟨x.a + y.a, x.b + y.b⟩

instance : Mul GoldenInt := ⟨mul⟩
instance : Add GoldenInt := ⟨add⟩

/-- `1 = 1 + 0·φ`. -/
def one : GoldenInt := ⟨1, 0⟩
/-- `φ = 0 + 1·φ` (the golden ratio, the residue's self-reference fixed point). -/
def phi : GoldenInt := ⟨0, 1⟩
/-- `ψ = φ − 1 = 1/φ = 2cos(2π/5)` (the pentagon / 5-fold rotational trace). -/
def psi : GoldenInt := ⟨-1, 1⟩

end GoldenInt

open GoldenInt

/-- ★★ **The golden self-reference quadratic** `φ² = φ + 1` — the algebraic residue of
    pointing (`Mobius213`, `seed/AXIOM/05_no_exterior.md` §5.6), here in `ℤ[φ]`. -/
theorem phi_quad : phi * phi = phi + one := by decide

/-- ★★★ **The pentagon trace is the conjugate golden root.**  `2cos(2π/5) = φ − 1` satisfies
    `x² + x − 1 = 0` (i.e. `(φ−1)² + (φ−1) = 1`) — the conjugate of `φ`'s `x² − x − 1 = 0`.
    The 5-fold rotational trace, on the crystallographically *forbidden* quasicrystal axis. -/
theorem pentagon_trace_quad : psi * psi + psi = one := by decide

/-- ★★★ **The pentagon trace is `1/φ`.**  `φ·(φ−1) = 1`, so the 5-fold rotational trace
    `2cos(2π/5) = φ − 1` is exactly the golden ratio's inverse — the continuous-rotation Lens,
    read on the forbidden 5-axis, returns the golden ratio (and its reciprocal). -/
theorem pentagon_trace_unit : phi * psi = one := by decide

/-- The two forbidden golden traces are reciprocal: `φ` (decagon, `2cos(π/5)`) and `φ−1`
    (pentagon, `2cos(2π/5)`) multiply to `1` — the single golden axis seen at its two
    forbidden orders `10` and `5`. -/
theorem golden_axis_reciprocal : phi * psi = one ∧ psi * phi = one :=
  ⟨by decide, by decide⟩

end E213.Lib.Math.Real213.PentagonGoldenTrace
