import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence
import E213.Meta.Int213.Order

/-!
# The golden boost has infinite order — the hyperbolic face never returns

`Mat2TraceRecurrence` gave the Lucas recurrence `tr(Gⁿ⁺²) = 3·tr(Gⁿ⁺¹) − tr(Gⁿ)` with seed `2, 3`.
Here that recurrence is run as an induction to prove the trace **strictly grows from a floor of 2**,
hence `Gⁿ⁺¹ ≠ I` for every `n` — the golden boost `G` (`disc = 5 > 0`) is **aperiodic**, the
hyperbolic infinite order made a theorem (contrast the elliptic `S⁴ = I`, `U⁶ = I`).  This is the
dynamic shadow of the discriminant sign: `disc < 0` ⇒ periodic floor, `disc > 0` ⇒ no return.  φ's
iterator never comes back; its trace is the unbounded Lucas sequence.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Phi.GoldenAperiodic

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace.Mat2 (tr I G)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence (pow golden_trace_recurrence golden_trace_seed)
open E213.Meta.Int213.Order
open E213.Meta.Int213 (zero_add)

/-- **The Lucas trace is monotone above 2.**  For every `n`, `2 ≤ tr(Gⁿ)` and `tr(Gⁿ) < tr(Gⁿ⁺¹)` —
    the orbit's trace strictly increases from the floor `tr(G⁰) = tr(I) = 2`. -/
theorem golden_trace_mono :
    ∀ n, (2 : Int) ≤ Mat2.tr (pow G n) ∧ Mat2.tr (pow G n) < Mat2.tr (pow G (n + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [golden_trace_seed.1]; exact le_refl 2
    · rw [golden_trace_seed.1, golden_trace_seed.2]; decide
  | succ n ih =>
    obtain ⟨hle, hlt⟩ := ih
    have hle' : (2 : Int) ≤ Mat2.tr (pow G (n + 1)) := le_of_lt (lt_of_le_of_lt hle hlt)
    refine ⟨hle', ?_⟩
    have p1 : (0 : Int) < Mat2.tr (pow G (n + 1)) - Mat2.tr (pow G n) := sub_pos_of_lt hlt
    have p2 : (0 : Int) < Mat2.tr (pow G (n + 1)) := lt_of_lt_of_le (by decide) hle'
    have key : Mat2.tr (pow G (n + 2)) - Mat2.tr (pow G (n + 1))
        = (Mat2.tr (pow G (n + 1)) - Mat2.tr (pow G n)) + Mat2.tr (pow G (n + 1)) := by
      rw [golden_trace_recurrence n]; ring_intZ
    have hXY := add_lt_add_right p1 (Mat2.tr (pow G (n + 1)))
    rw [zero_add] at hXY
    have hpos : (0 : Int)
        < (Mat2.tr (pow G (n + 1)) - Mat2.tr (pow G n)) + Mat2.tr (pow G (n + 1)) :=
      lt_trans p2 hXY
    rw [← key] at hpos
    exact lt_of_sub_pos hpos

/-- `tr(Gⁿ⁺¹) > 2` for every `n` — the trace exceeds `tr(I) = 2` past the start. -/
theorem golden_trace_gt_two (n : Nat) : (2 : Int) < Mat2.tr (pow G (n + 1)) :=
  lt_of_le_of_lt (golden_trace_mono n).1 (golden_trace_mono n).2

/-- ★★★★ **The golden boost is aperiodic.**  `Gⁿ⁺¹ ≠ I` for every `n`: the iterate's trace exceeds
    `tr(I) = 2`, so it can never be the identity.  The hyperbolic face has **infinite order** — no
    periodic floor, the dynamic signature of `disc = 5 > 0` (contrast `S⁴ = I`, `U⁶ = I`). -/
theorem golden_aperiodic (n : Nat) : pow G (n + 1) ≠ I := by
  intro hEq
  have htr : Mat2.tr (pow G (n + 1)) = Mat2.tr I := by rw [hEq]
  have hI : Mat2.tr (I : Mat2) = 2 := by decide
  rw [hI] at htr
  have hgt := golden_trace_gt_two n
  rw [htr] at hgt
  exact lt_irrefl 2 hgt

end E213.Lib.Math.NumberSystems.Real213.Phi.GoldenAperiodic
