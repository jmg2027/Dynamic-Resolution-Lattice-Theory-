import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence
import E213.Meta.Int213.Order

/-!
# The elliptic trace is periodic — the mirror of the golden boost's growth

`GoldenAperiodic` ran the trace recurrence to show the hyperbolic `tr(Gⁿ)` grows without bound
(`G` aperiodic).  The elliptic generator `S` (`tr = 0`, `det = 1`, `disc = −4 < 0`) is the mirror:
the recurrence `tr(Sⁿ⁺²) = tr(S)·tr(Sⁿ⁺¹) − det(S)·tr(Sⁿ)` collapses to

  `tr(Sⁿ⁺²) = − tr(Sⁿ)`   (`S_trace_recurrence`),

so the trace is **period 4** (`S_trace_period4`) and **bounded** — `tr(Sⁿ)` cycles through
`2, 0, −2, 0` (`S_trace_seed`).  Boundedness is the elliptic dynamic signature (`disc < 0`), exactly
opposite the hyperbolic unbounded Lucas growth (`disc > 0`).  The matrix itself has period 4
(`S⁴ = I`, `ModularElliptic.modular_generator_orders`); the trace is the diagnostic that reads
periodic-vs-aperiodic off the sign of `disc`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.EllipticTracePeriodic

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace.Mat2 (tr det S)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence (pow trace_recurrence)
open E213.Meta.Int213 (zero_mul)
open E213.Meta.Int213.PolyIntM (one_mulZ)
open E213.Meta.Int213.Order (zero_sub)

/-- `− − x = x` (constructor-matched, ∅-axiom). -/
private theorem nneg : ∀ (x : Int), - -x = x
  | Int.ofNat 0 => rfl
  | Int.ofNat (_ + 1) => rfl
  | Int.negSucc _ => rfl

/-- ★★★ **The elliptic trace recurrence collapses to a sign flip.**  `tr(Sⁿ⁺²) = − tr(Sⁿ)`
    (`tr S = 0`, `det S = 1`). -/
theorem S_trace_recurrence (n : Nat) : Mat2.tr (pow S (n + 2)) = - Mat2.tr (pow S n) := by
  have ht : Mat2.tr S = 0 := by decide
  have hd : Mat2.det S = 1 := by decide
  rw [trace_recurrence S n, ht, hd, zero_mul, one_mulZ, zero_sub]

/-- ★★★ **The elliptic trace has period 4.**  `tr(Sⁿ⁺⁴) = tr(Sⁿ)` — two sign flips return. -/
theorem S_trace_period4 (n : Nat) : Mat2.tr (pow S (n + 4)) = Mat2.tr (pow S n) := by
  rw [show n + 4 = n + 2 + 2 from rfl, S_trace_recurrence (n + 2), S_trace_recurrence n, nneg]

/-- The four trace values: `tr(S⁰), tr(S¹), tr(S²), tr(S³) = 2, 0, −2, 0` — bounded, `|tr| ≤ 2`. -/
theorem S_trace_seed :
    Mat2.tr (pow S 0) = 2 ∧ Mat2.tr (pow S 1) = 0
    ∧ Mat2.tr (pow S 2) = -2 ∧ Mat2.tr (pow S 3) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★ **The elliptic trace is periodic and bounded — the mirror of golden growth.**  `tr(Sⁿ⁺²) =
    −tr(Sⁿ)`, hence period 4, cycling `2, 0, −2, 0` (`|tr| ≤ 2`).  Boundedness is the `disc < 0`
    elliptic signature, opposite the `disc > 0` hyperbolic unbounded growth (`GoldenAperiodic`). -/
theorem elliptic_trace_periodic :
    (∀ n, Mat2.tr (pow S (n + 2)) = - Mat2.tr (pow S n))
    ∧ (∀ n, Mat2.tr (pow S (n + 4)) = Mat2.tr (pow S n))
    ∧ (Mat2.tr (pow S 0) = 2 ∧ Mat2.tr (pow S 1) = 0
        ∧ Mat2.tr (pow S 2) = -2 ∧ Mat2.tr (pow S 3) = 0) :=
  ⟨S_trace_recurrence, S_trace_period4, S_trace_seed⟩

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.EllipticTracePeriodic
