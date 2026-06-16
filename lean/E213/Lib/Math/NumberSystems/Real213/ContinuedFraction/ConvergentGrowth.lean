import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuedFractionFloor

/-!
# The Fibonacci floor on continued-fraction convergent denominators (∅-axiom)

`ContinuedFractionFloor` proves the *step* recurrence `q_{n+1} + q_n ≤ q_{n+2}`
(`cfQn_fib`) and `ContinuedFractionModulus` the crude `n ≤ q_n` (`cfQn_ge_self`).
ABSENT until now: the **closed-form geometric** lower bound `fib n ≤ q_n` — the
genuine approximation-quality floor.  For partial quotients `≥ 1` the convergent
denominators grow at least like Fibonacci, so the convergent gaps
`1/(q_n q_{n+1})` shrink at least like `φ^{-2n}` (geometrically), not merely like
`1/n²`.  This closes that bound, plus the companion non-strict denominator
monotonicity `q_n ≤ q_{n+1}` (also absent — the tree had only the additive step).

Together with `ContinuantDeterminant` (det `(−1)ⁿ`), `ConvergentCoprime`
(`gcd(pₙ,qₙ)=1`) and `ConvergentRecurrence` (the three-term recurrence), this
rounds out the convergent-arithmetic + growth core of CF approximation theory.

`fibN` is the standard local `Nat` Fibonacci (the CF tree is self-contained;
importing the `Combinatorics` Fibonacci would be a heavy cross-dependency).
All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentGrowth

open E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuedFractionFloor
  (cfQn cfQn_pos cfQn_fib)

/-- Native `Nat` Fibonacci, the standard seed `fib 0 = 0`, `fib 1 = 1`. -/
def fibN : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibN (n + 1) + fibN n

/-- ★ **The Fibonacci floor on convergent denominators** (coupled depth-2 form):
    `fib n ≤ q_n` *and* `fib (n+1) ≤ q_{n+1}` simultaneously (the depth-2 recurrences
    of `fib` and `q` are coupled, so both are carried).  For partial quotients `≥ 1`
    the denominators grow at least geometrically.  Strictly stronger than the existing
    `cfQn_ge_self` (`n ≤ q_n`). -/
theorem cfQn_ge_fib_pair (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) :
    ∀ n, fibN n ≤ cfQn a n ∧ fibN (n + 1) ≤ cfQn a (n + 1)
  | 0 =>
      -- fib 0 = 0 ≤ q₀, fib 1 = 1 ≤ q₁  (q₁ = a 1 ≥ 1)
      ⟨Nat.zero_le _, ha 0⟩
  | n + 1 => by
      obtain ⟨ih0, ih1⟩ := cfQn_ge_fib_pair a ha n
      refine ⟨ih1, ?_⟩
      -- fib (n+2) = fib (n+1) + fib n ≤ q_{n+1} + q_n ≤ q_{n+2}
      show fibN (n + 1) + fibN n ≤ cfQn a (n + 2)
      have hsum : fibN (n + 1) + fibN n ≤ cfQn a (n + 1) + cfQn a n :=
        Nat.add_le_add ih1 ih0
      exact Nat.le_trans hsum (cfQn_fib a ha n)

/-- ★ **The Fibonacci floor, single-index form**: `fib n ≤ q_n`. -/
theorem cfQn_ge_fib (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) (n : Nat) :
    fibN n ≤ cfQn a n :=
  (cfQn_ge_fib_pair a ha n).1

/-- ★ **Non-strict monotonicity of the convergent denominators**: `q_n ≤ q_{n+1}`.
    (For partial quotients `≥ 1`; from `q_{n+2} = a_{n+2}·q_{n+1} + q_n ≥ q_{n+1}`, with
    the `q₀ = 1 ≤ a₁ = q₁` base.)  Absent from the CF tree, which had only the additive
    step `cfQn_fib`. -/
theorem cfQn_le_succ (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) :
    ∀ n, cfQn a n ≤ cfQn a (n + 1)
  | 0 =>
      -- q₀ = 1 ≤ a 1 = q₁
      ha 0
  | n + 1 => by
      -- q_{n+1} ≤ a_{n+2}·q_{n+1} + q_n = q_{n+2}
      show cfQn a (n + 1) ≤ a (n + 2) * cfQn a (n + 1) + cfQn a n
      have h1 : cfQn a (n + 1) ≤ a (n + 2) * cfQn a (n + 1) :=
        Nat.le_mul_of_pos_left (cfQn a (n + 1)) (ha (n + 1))
      exact Nat.le_trans h1 (Nat.le_add_right _ _)

/-! ## Concrete smoke checks (the bound is real, not vacuous) -/

/-- `fib 6 = 8`, `fib 7 = 13`. -/
theorem fibN_smoke : fibN 6 = 8 ∧ fibN 7 = 13 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The all-`1`s sequence (φ): `q₅ = 8 = fib 6` — the floor is attained (sharp). -/
theorem cfQn_ones_smoke : cfQn (fun _ => 1) 5 = 8 := by decide

end E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentGrowth
