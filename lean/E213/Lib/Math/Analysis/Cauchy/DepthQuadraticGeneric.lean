import E213.Meta.Nat.PolyNat
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances

/-!
# DepthQuadraticGeneric — every quadratic discrete polynomial has divergence-depth 2

`DepthAperyCubic` pinned the depth of the *specific* ζ(2) recurrence coefficients
(`(n+1)²`, `11n²+11n+3`, `n²`).  This file proves the **uniform** statement they are
instances of:

> `quadratic_polyDepth A B C : polyDepth 2 (fun n => A·n² + B·n + C)` — for *every*
> `A B C : ℕ`, the quadratic `A·n²+B·n+C` reaches its constant floor (`2A`) after exactly
> two finite differences.

This caps the entire **order-2, degree-2 Apéry-like (Zagier sporadic) family** in one
∅-axiom theorem: ζ(2)-Apéry, Domb, Almkvist–Zudilin, Catalan-`β(2)`, … all have
`(an²+bn+c)` recurrence coefficients, and every such coefficient is depth-2 here, with no
case-by-case coefficient transcription.

The proof transfers the general `newton_polyDepth` ("degree-`d` Newton form ⟹ depth `d`")
of `DepthPRecursiveInstances` along the pointwise identity `A·n²+B·n+C = newton c 2 n`,
where the Newton coefficients are `c = (C, A+B, 2A)` (from `n² = 2·binom n 2 + n` and
`binom n 1 = n`).  The transfer needs no truncating subtraction; the one nonlinear `ℕ`
identity `(n+1)² = n² + 2n + 1` is discharged by the reflection prover `Meta.Nat.PolyNat`.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DepthQuadraticGeneric

open E213.Meta.Nat.PolyNat (poly_id)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth liftK_congr)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances (binom newton binom_zero_right newton_polyDepth)
open E213.Tactic.NatHelper (add_mul mul_assoc)

/-! ## §1 — binomial-column closed forms (for the `DepthPRecursiveInstances.binom`) -/

/-- `binom n 1 = n` (Pascal, by induction). -/
theorem binom_one : ∀ n, binom n 1 = n
  | 0   => rfl
  | n+1 => by
      show binom n 0 + binom n 1 = n + 1
      rw [binom_zero_right n, binom_one n, Nat.add_comm 1 n]

/-- Pascal step at column 2: `binom (n+1) 2 = n + binom n 2`. -/
theorem binom_succ_two (n : Nat) : binom (n+1) 2 = n + binom n 2 := by
  show binom n 1 + binom n 2 = n + binom n 2
  rw [binom_one n]

/-- The square as a Newton (binomial) combination: `n² = 2·binom n 2 + n` — the
    subtraction-free form of `binom n 2 = n(n−1)/2`. -/
theorem sq_eq : ∀ n, n*n = 2 * binom n 2 + n
  | 0   => rfl
  | n+1 => by
      have sq_succ : (n+1)*(n+1) = n*n + 2*n + 1 :=
        poly_id (.mul (.add .X (.C 1)) (.add .X (.C 1)))
                (.add (.add (.mul .X .X) (.mul (.C 2) .X)) (.C 1)) rfl n
      show (n+1)*(n+1) = 2 * binom (n+1) 2 + (n+1)
      rw [binom_succ_two n, Nat.mul_add 2 n (binom n 2), sq_succ, sq_eq n]
      -- 2·binom n 2 + n + 2n + 1 = 2n + 2·binom n 2 + (n+1)
      exact reorderA (2 * binom n 2) n (2*n)
where
  /-- `U + n + W + 1 = W + U + (n+1)` — the additive reshuffle closing the `sq_eq`
      induction step. -/
  reorderA (U n W : Nat) : U + n + W + 1 = W + U + (n+1) := by
    rw [← Nat.add_assoc (W+U) n 1, Nat.add_assoc U n W, Nat.add_comm n W,
        ← Nat.add_assoc U W n, Nat.add_comm U W]

/-! ## §2 — the pointwise Newton form of a quadratic -/

/-- The Newton coefficients of `A·n²+B·n+C`: `(c 0, c 1, c 2) = (C, A+B, 2A)`. -/
def quadCoeff (A B C : Nat) : Nat → Nat
  | 0   => C
  | 1   => A + B
  | _   => 2 * A

/-- ★★ **A quadratic is its Newton form.**  `A·n² + B·n + C = newton (quadCoeff A B C) 2
    n` pointwise — using `binom n 1 = n` and `n² = 2·binom n 2 + n`, then the collect step is
    one `ring_nat` (the multivariate reflection tactic; was a hand-written 4-term reorder). -/
theorem quad_eq (A B C n : Nat) :
    A*n*n + B*n + C = newton (quadCoeff A B C) 2 n := by
  show A*n*n + B*n + C = (C + (A+B) * binom n 1) + 2*A * binom n 2
  rw [binom_one n, mul_assoc A n n, sq_eq n]
  ring_nat

/-! ## §3 — depth-2 transfer -/

/-- `polyDepth` respects pointwise equality (transfer along `liftK_congr`). -/
theorem polyDepth_congr (d : Nat) (f g : Nat → Nat) (h : ∀ n, f n = g n)
    (hg : polyDepth d g) : polyDepth d f := by
  intro n
  rw [liftK_congr d f g h n, liftK_congr d f g h 0]
  exact hg n

/-- ★★★ **Every quadratic discrete polynomial has divergence-depth 2.**  For all
    `A B C : ℕ`, `polyDepth 2 (fun n => A·n²+B·n+C)` — the entire order-2, degree-2
    Apéry-like (Zagier sporadic) family of recurrence coefficients in one ∅-axiom
    statement (ζ(2)-Apéry, Domb, Almkvist–Zudilin, Catalan-`β(2)`, …), via the Newton-form
    transfer of `newton_polyDepth`. -/
theorem quadratic_polyDepth (A B C : Nat) : polyDepth 2 (fun n => A*n*n + B*n + C) :=
  polyDepth_congr 2 _ _ (fun n => quad_eq A B C n) (newton_polyDepth (quadCoeff A B C) 2)

end E213.Lib.Math.Analysis.Cauchy.DepthQuadraticGeneric
