import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2CayleyHamilton
import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc

/-!
# The trace recurrence — Cayley–Hamilton iterated, the bridge to dynamics

Cayley–Hamilton (`M² = tr·M − det·I`) plus associativity (`Mat2Assoc.mul_assoc`) give the **trace
(Lucas / Chebyshev) recurrence** of the matrix powers:

  `tr(Mⁿ⁺²) = tr(M) · tr(Mⁿ⁺¹) − det(M) · tr(Mⁿ)`   (`trace_recurrence`).

This is the static dial set in motion: the sequence `tr(Mⁿ)` is a constant-coefficient
(`C`-finite / holonomic) recurrence whose characteristic equation is the Cayley–Hamilton quadratic
`λ² − tr·λ + det`, with discriminant `disc = tr² − 4·det`.  The trichotomy now reads dynamically:

  - **elliptic** (`disc < 0`): `tr(Mⁿ)` is bounded/periodic — the orbit has finite order (`S⁴ = I`,
    `U⁶ = I`);
  - **hyperbolic** (`disc > 0`): `tr(Mⁿ)` grows — infinite order, no periodic floor.

The golden boost `G = [[2,1],[1,1]]` (`det = 1`, `tr = 3`) gives the Lucas recurrence
`tr(Gⁿ⁺²) = 3·tr(Gⁿ⁺¹) − tr(Gⁿ)` (`golden_trace_recurrence`) with seed `2, 3`
(`golden_trace_seed`): the sequence `2, 3, 7, 18, 47, …` is strictly increasing, so `tr(Gⁿ) > 2 =
tr(I)` for `n ≥ 1` — `G` is aperiodic, the hyperbolic face's infinite order, the dynamic shadow of
`disc = 5 > 0`.  φ's iterator never returns; the Lucas numbers are its trace.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace.Mat2 (mul tr det I G)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2CayleyHamilton (charComb cayley_hamilton)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc (mul_assoc)

/-- Matrix power `Mⁿ` (right-multiplication). -/
def pow (M : Mat2) : Nat → Mat2
  | 0 => I
  | n + 1 => mul (pow M n) M

/-- Trace of `A · (tr(M)·M − det(M)·I)` expands by linearity:
    `tr(A · charComb M) = tr(M)·tr(A·M) − det(M)·tr(A)`. -/
theorem tr_mul_charComb (A M : Mat2) :
    Mat2.tr (mul A (charComb M)) = Mat2.tr M * Mat2.tr (mul A M) - Mat2.det M * Mat2.tr A := by
  rcases A with ⟨a, b, c, d⟩
  rcases M with ⟨e, f, g, h⟩
  show (a * ((e + h) * e - (e * h - f * g)) + b * ((e + h) * g))
      + (c * ((e + h) * f) + d * ((e + h) * h - (e * h - f * g)))
      = (e + h) * ((a * e + b * g) + (c * f + d * h)) - (e * h - f * g) * (a + d)
  ring_intZ

/-- ★★★★ **The trace recurrence.**  `tr(Mⁿ⁺²) = tr(M)·tr(Mⁿ⁺¹) − det(M)·tr(Mⁿ)` — Cayley–Hamilton
    iterated (via `mul_assoc`).  The matrix powers' traces are a constant-coefficient recurrence whose
    characteristic discriminant is the dial `disc = tr² − 4·det`. -/
theorem trace_recurrence (M : Mat2) (n : Nat) :
    Mat2.tr (pow M (n + 2)) = Mat2.tr M * Mat2.tr (pow M (n + 1)) - Mat2.det M * Mat2.tr (pow M n) := by
  have step : pow M (n + 2) = mul (pow M n) (charComb M) := by
    show mul (mul (pow M n) M) M = mul (pow M n) (charComb M)
    rw [mul_assoc, cayley_hamilton]
  rw [step, tr_mul_charComb]
  rfl

/-! ## The golden boost: the Lucas recurrence, infinite order -/

/-- ★★★ **The golden boost satisfies the Lucas recurrence.**  `tr(Gⁿ⁺²) = 3·tr(Gⁿ⁺¹) − tr(Gⁿ)`
    (`tr G = 3`, `det G = 1`) — the trace of φ's iterator is the Lucas sequence. -/
theorem golden_trace_recurrence (n : Nat) :
    Mat2.tr (pow G (n + 2)) = 3 * Mat2.tr (pow G (n + 1)) - Mat2.tr (pow G n) := by
  have h := trace_recurrence G n
  have ht : Mat2.tr G = 3 := by decide
  have hd : Mat2.det G = 1 := by decide
  rw [ht, hd, E213.Meta.Int213.PolyIntM.one_mulZ] at h
  exact h

/-- The Lucas seed: `tr(G⁰) = 2` (`= tr I`), `tr(G¹) = 3`.  With the recurrence this is `2, 3, 7,
    18, 47, …` — strictly increasing, so `tr(Gⁿ) > 2` for `n ≥ 1`: `G` is aperiodic (infinite order),
    the hyperbolic face's dynamic signature. -/
theorem golden_trace_seed : Mat2.tr (pow G 0) = 2 ∧ Mat2.tr (pow G 1) = 3 := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence
