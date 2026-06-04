import E213.Lib.Math.Real213.EllipticTracePeriodic

/-!
# The second elliptic trace has period 6 — the `{4, 6}` elliptic orders, side by side

`EllipticTracePeriodic` showed `S` (`tr 0`) gives a period-4 bounded trace.  The second elliptic
generator `U` (`tr 1`, `det 1`, `disc = 1 − 4 = −3 < 0`) gives the period-6 companion.  Its trace
recurrence is `tr(Uⁿ⁺²) = tr(Uⁿ⁺¹) − tr(Uⁿ)` (`U_trace_recurrence`), which yields
`tr(Uⁿ⁺³) = − tr(Uⁿ)` (`U_trace_step3`), hence **period 6** (`U_trace_period6`): the trace cycles
`2, 1, −1, −2, −1, 1` (`U_trace_seed`), bounded.  So the two elliptic generators carry the trace
periods `4` and `6` — the orders `|ℤ[i]^×| = 4` and `|ℤ[ω]^×| = 6`, the `{4,6}` Gaussian/Eisenstein
axis — both bounded (`disc < 0`), against the hyperbolic unbounded growth (`GoldenAperiodic`).
-/

namespace E213.Lib.Math.Real213.UTracePeriodic

open E213.Lib.Math.Real213.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.Real213.HyperbolicEllipticTrace.Mat2 (tr det U S)
open E213.Lib.Math.Real213.Mat2TraceRecurrence (pow trace_recurrence)
open E213.Lib.Math.Real213.EllipticTracePeriodic (S_trace_period4)
open E213.Meta.Int213.PolyIntM (one_mulZ)

/-- `− − x = x` (constructor-matched, ∅-axiom). -/
private theorem nneg : ∀ (x : Int), - -x = x
  | Int.ofNat 0 => rfl
  | Int.ofNat (_ + 1) => rfl
  | Int.negSucc _ => rfl

/-- ★★★ **The order-6 trace recurrence.**  `tr(Uⁿ⁺²) = tr(Uⁿ⁺¹) − tr(Uⁿ)` (`tr U = 1`,
    `det U = 1`). -/
theorem U_trace_recurrence (n : Nat) :
    Mat2.tr (pow U (n + 2)) = Mat2.tr (pow U (n + 1)) - Mat2.tr (pow U n) := by
  have ht : Mat2.tr U = 1 := by decide
  have hd : Mat2.det U = 1 := by decide
  rw [trace_recurrence U n, ht, hd, one_mulZ, one_mulZ]

/-- ★★★ **Three steps flip the sign.**  `tr(Uⁿ⁺³) = − tr(Uⁿ)` — the order-6 analogue of `S`'s
    two-step flip. -/
theorem U_trace_step3 (n : Nat) : Mat2.tr (pow U (n + 3)) = - Mat2.tr (pow U n) := by
  have h1 : Mat2.tr (pow U (n + 3)) = Mat2.tr (pow U (n + 2)) - Mat2.tr (pow U (n + 1)) :=
    U_trace_recurrence (n + 1)
  have h2 : Mat2.tr (pow U (n + 2)) = Mat2.tr (pow U (n + 1)) - Mat2.tr (pow U n) :=
    U_trace_recurrence n
  rw [h1, h2]; ring_intZ

/-- ★★★ **The order-6 trace has period 6.**  `tr(Uⁿ⁺⁶) = tr(Uⁿ)` — two sign flips return. -/
theorem U_trace_period6 (n : Nat) : Mat2.tr (pow U (n + 6)) = Mat2.tr (pow U n) := by
  have h1 : Mat2.tr (pow U (n + 6)) = - Mat2.tr (pow U (n + 3)) := U_trace_step3 (n + 3)
  have h2 : Mat2.tr (pow U (n + 3)) = - Mat2.tr (pow U n) := U_trace_step3 n
  rw [h1, h2, nneg]

/-- The six trace values: `2, 1, −1, −2, −1, 1` — bounded, `|tr| ≤ 2`. -/
theorem U_trace_seed :
    Mat2.tr (pow U 0) = 2 ∧ Mat2.tr (pow U 1) = 1 ∧ Mat2.tr (pow U 2) = -1
    ∧ Mat2.tr (pow U 3) = -2 ∧ Mat2.tr (pow U 4) = -1 ∧ Mat2.tr (pow U 5) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★ **The two elliptic generators carry trace periods 4 and 6.**  `S` (`|ℤ[i]^×| = 4`) and `U`
    (`|ℤ[ω]^×| = 6`) — both bounded (`disc < 0`), the Gaussian/Eisenstein `{4,6}` axis, against the
    hyperbolic unbounded growth.  The trace reads the elliptic orders as its periods. -/
theorem elliptic_orders_four_and_six :
    (∀ n, Mat2.tr (pow S (n + 4)) = Mat2.tr (pow S n))
    ∧ (∀ n, Mat2.tr (pow U (n + 6)) = Mat2.tr (pow U n)) :=
  ⟨S_trace_period4, U_trace_period6⟩

end E213.Lib.Math.Real213.UTracePeriodic
