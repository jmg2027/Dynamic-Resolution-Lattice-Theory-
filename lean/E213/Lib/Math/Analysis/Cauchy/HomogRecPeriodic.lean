import E213.Lib.Math.Analysis.Cauchy.MorseHedlund

/-!
# Eventually periodic ⟹ `HomogRec` — the easy half of the bounded characterization

`MorseHedlund.bool_autoRec_iff_evPeriodic` gives, for the autonomous machine class, `AutoRec ⟺
EvPeriodic` (both directions ∅-axiom).  For the *time-varying* `HomogRec` class one direction is
elementary and one is the deep classical theorem.  This file closes the **elementary** direction:

> `evPeriodic_homogRec : EvPeriodic a → HomogRec (b2n∘a embedding)`.

Construction (using that `HomogRec` admits an *arbitrary* leading coefficient and right-hand side,
not just polynomial ones): order `k = p`, with the prefix `< N` killed by a guard —
`lead n = if n < N then 0 else 1` and `R n w = if n < N then 0 else w 0`.  Then the recurrence
`lead n · a(n+p) = R n (window)` holds for *every* `n` (trivially on the prefix where `lead = 0`,
and as `a(n+p) = a(n)` past `N`), `lead` is nonzero past `N`, and `R` vanishes on the zero window.

Paired with the (classical, **not** ∅-axiom) converse "bounded `HomogRec` ⟹ eventually periodic",
this pins the bounded picture: `EvPeriodic ⟹ HomogRec` (here) and `EvPeriodic ⟺ AutoRec` (there),
so the *only* non-elementary step left is exactly the bounded-P-recursive theorem — see the verdict
essay `theory/essays/non_holonomicity_as_finite_state_escape.md`.
-/

namespace E213.Lib.Math.Analysis.Cauchy.HomogRecPeriodic

open E213.Lib.Math.Analysis.Cauchy.MorseHedlund (EvPeriodic b2n)
open E213.Lib.Math.Analysis.Cauchy.ZeroRunNonHolonomic (HomogRec)

/-- **Eventually periodic ⟹ `HomogRec`.**  A period-`p`, threshold-`N` `Bool`-sequence's `{0,1}`
    embedding satisfies the homogeneous order-`p` recurrence `lead·a(n+p) = R(n, window)` with the
    prefix `< N` killed by an `if`-guarded leading coefficient. -/
theorem evPeriodic_homogRec (a : Nat → Bool) (h : EvPeriodic a) :
    HomogRec (fun n => ((b2n (a n) : Nat) : Int)) := by
  obtain ⟨p, hp, N, hper⟩ := h
  refine ⟨p, fun n => if n < N then 0 else 1, fun n w => if n < N then 0 else w 0, N, ?_, ?_, ?_⟩
  · -- lead nonzero past N
    intro n hn
    have hnlt : ¬ n < N := fun hlt => Nat.lt_irrefl n (Nat.lt_of_lt_of_le hlt hn)
    show (if n < N then (0 : Int) else 1) ≠ 0
    rw [if_neg hnlt]; exact (by decide : (1 : Int) ≠ 0)
  · -- R vanishes on the zero window
    intro n w hw
    show (if n < N then (0 : Int) else w 0) = 0
    rcases Nat.lt_or_ge n N with hlt | hge
    · rw [if_pos hlt]
    · rw [if_neg (fun hlt => Nat.lt_irrefl n (Nat.lt_of_lt_of_le hlt hge))]
      exact hw 0 hp
  · -- the recurrence holds for every n
    intro n
    rcases Nat.lt_or_ge n N with hlt | hge
    · show (if n < N then (0 : Int) else 1) * ((b2n (a (n + p)) : Nat) : Int)
          = (if n < N then (0 : Int) else ((b2n (a (n + 0)) : Nat) : Int))
      rw [if_pos hlt, if_pos hlt]; exact E213.Meta.Int213.zero_mul _
    · have hnlt : ¬ n < N := fun hlt => Nat.lt_irrefl n (Nat.lt_of_lt_of_le hlt hge)
      show (if n < N then (0 : Int) else 1) * ((b2n (a (n + p)) : Nat) : Int)
          = (if n < N then (0 : Int) else ((b2n (a (n + 0)) : Nat) : Int))
      rw [if_neg hnlt, if_neg hnlt, Nat.add_zero, hper n hge,
          E213.Meta.Int213.mul_comm, E213.Meta.Int213.mul_one]

end E213.Lib.Math.Analysis.Cauchy.HomogRecPeriodic
