/-!
# Continued fractions as FSM (213-native)

Continued-fraction expansion of a positive rational `p/q` is the
output stream of an FSM on the dyadic-encoded numerator/denominator
pair.  The Euclidean step `(n, d) ↦ (d, n mod d)` is the transition;
the integer-quotient `n / d` is the output.

  Value `p / q = a₀ + 1/(a₁ + 1/(a₂ + 1/(a₃ + ...)))`
  with `aₖ = nₖ / dₖ` at step `k`, and `(n_{k+1}, d_{k+1}) =
  (dₖ, nₖ mod dₖ)`.

Termination: when `d = 0`, the expansion stops (the value is the
last `a`).  For rationals this terminates; for irrationals on
Dedekind-cut input, the expansion is non-terminating but each
step is finite.

This file makes the FSM realisation explicit + computes the
expansions for a few 213-relevant rationals (Cabibbo 5/22,
π ≈ 22/7, CKM-δ rational 176/147).

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.ContinuedFraction

/-- State of the continued-fraction FSM: `(numerator, denominator)`. -/
abbrev CFState : Type := Nat × Nat

/-- Single Euclidean step: `(n, d) ↦ (d, n mod d)`.  When `d = 0`
    we leave the state unchanged (terminal state). -/
def cfStep (s : CFState) : CFState :=
  if s.2 = 0 then s else (s.2, s.1 % s.2)

/-- Output at the current state: integer quotient `n / d`, or `0`
    if `d = 0` (terminal). -/
def cfDigit (s : CFState) : Nat :=
  if s.2 = 0 then 0 else s.1 / s.2

/-- Iterate `cfStep` `n` times. -/
def cfStepIter : Nat → CFState → CFState
  | 0,     s => s
  | n + 1, s => cfStepIter n (cfStep s)

/-- The `k`-th continued-fraction coefficient of `p / q`. -/
def cfCoeff (p q : Nat) (k : Nat) : Nat :=
  cfDigit (cfStepIter k (p, q))

/-- The first `k` coefficients as a list (prefix of the expansion). -/
def cfExpansion (p q : Nat) : Nat → List Nat
  | 0     => []
  | n + 1 => cfCoeff p q 0 :: cfExpansion (cfStepIter 1 (p, q)).1
                                          (cfStepIter 1 (p, q)).2 n

/-! ## Smoke tests at 213-relevant rationals -/

/-- `5 / 22 = [0; 4, 2, 2]`: the Cabibbo angle bare value. -/
theorem cf_cabibbo_5_22 :
    cfCoeff 5 22 0 = 0
    ∧ cfCoeff 5 22 1 = 4
    ∧ cfCoeff 5 22 2 = 2
    ∧ cfCoeff 5 22 3 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `22 / 7 = [3; 7]`: Archimedean π approximation. -/
theorem cf_pi_22_7 :
    cfCoeff 22 7 0 = 3
    ∧ cfCoeff 22 7 1 = 7 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `22 / 7` terminates at step 2 (denominator becomes 0). -/
theorem cf_pi_22_7_terminates :
    (cfStepIter 2 (22, 7)).2 = 0 := by decide

/-- `176 / 147 = [1; 5, 4, ...]`: CKM-δ rational approximation. -/
theorem cf_ckm_176_147 :
    cfCoeff 176 147 0 = 1
    ∧ cfCoeff 176 147 1 = 5 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `21 / 8 = [2; 1, 1, 1, 2]`: Fibonacci-convergent φ² approximation. -/
theorem cf_phi_sq_21_8 :
    cfCoeff 21 8 0 = 2
    ∧ cfCoeff 21 8 1 = 1
    ∧ cfCoeff 21 8 2 = 1
    ∧ cfCoeff 21 8 3 = 1
    ∧ cfCoeff 21 8 4 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★ **Fibonacci-convergent fingerprint**: the leading coefficients
    of `F_{n+1} / F_n` (Fibonacci convergents to φ) are all `1`.
    Concretely: `5 / 3 = [1; 1, 2]`, `8 / 5 = [1; 1, 1, 2]`,
    `13 / 8 = [1; 1, 1, 1, 2]`. -/
theorem cf_fib_convergent_5_3 :
    cfCoeff 5 3 0 = 1 ∧ cfCoeff 5 3 1 = 1 ∧ cfCoeff 5 3 2 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem cf_fib_convergent_8_5 :
    cfCoeff 8 5 0 = 1
    ∧ cfCoeff 8 5 1 = 1
    ∧ cfCoeff 8 5 2 = 1
    ∧ cfCoeff 8 5 3 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem cf_fib_convergent_13_8 :
    cfCoeff 13 8 0 = 1
    ∧ cfCoeff 13 8 1 = 1
    ∧ cfCoeff 13 8 2 = 1
    ∧ cfCoeff 13 8 3 = 1
    ∧ cfCoeff 13 8 4 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## FSM basic properties -/

/-- The step is identity at the terminal state `(n, 0)`. -/
theorem cfStep_terminal (n : Nat) : cfStep (n, 0) = (n, 0) := by
  show (if (n, 0).2 = 0 then (n, 0) else _) = (n, 0)
  rfl

/-- The digit is 0 at the terminal state `(n, 0)`. -/
theorem cfDigit_terminal (n : Nat) : cfDigit (n, 0) = 0 := by
  show (if (n, 0).2 = 0 then 0 else _) = 0
  rfl

/-- Coprime-fraction termination smoke: `gcd(5, 22) = 1` ⇒
    expansion has 4 terms `[0; 4, 2, 2]` and `cfStepIter 4 (5, 22)`
    lands in the terminal state. -/
theorem cf_cabibbo_terminates : (cfStepIter 4 (5, 22)).2 = 0 := by
  decide

/-! ## Capstone -/

/-- ★★★★ **Continued-fraction FSM capstone**.

    Bundles: (a) FSM state `(n, d)` + step `(d, n mod d)` + digit
    `n / d`, (b) terminal behavior, (c) concrete expansions for
    213-relevant rationals: Cabibbo `5/22 = [0; 4, 2, 2]`,
    Archimedean `22/7 = [3; 7]`, CKM-δ `176/147 = [1; 5, ...]`,
    Fibonacci-convergent `φ² ≈ 21/8 = [2; 1, 1, 1, 2]`.

    Reading: every rational that appears in DRLT precision tables
    (Cabibbo, CKM δ, π approximations, Fibonacci convergents) has
    its continued-fraction expansion as a finite FSM output stream.
    The Euclidean algorithm IS the FSM transition. -/
theorem continued_fraction_fsm_capstone :
    -- (a) Cabibbo 5/22 = [0; 4, 2, 2]
    cfCoeff 5 22 0 = 0
    ∧ cfCoeff 5 22 1 = 4
    ∧ cfCoeff 5 22 2 = 2
    ∧ cfCoeff 5 22 3 = 2
    -- (b) π ≈ 22/7 = [3; 7]
    ∧ cfCoeff 22 7 0 = 3
    ∧ cfCoeff 22 7 1 = 7
    -- (c) CKM-δ 176/147 = [1; 5, ...]
    ∧ cfCoeff 176 147 0 = 1
    ∧ cfCoeff 176 147 1 = 5
    -- (d) φ² ≈ 21/8 = [2; 1, 1, 1, 2]
    ∧ cfCoeff 21 8 0 = 2
    ∧ cfCoeff 21 8 4 = 2
    -- (e) Termination at coprime input
    ∧ (cfStepIter 4 (5, 22)).2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.DyadicFSM.ContinuedFraction
