import E213.Math.Cohomology.Dyadic.Pisano.Predictor
import E213.Math.Cohomology.Dyadic.Fib.PisanoCapstone

/-!
# Cross-recurrence relation: Fib predictor = 2 × Pell predictor

The Fibonacci-Pisano and Pell-Pisano formulas, derived independently
from the same Legendre lens (Δ = 5), satisfy a clean **structural
doubling identity**:

  fib_pisano_predict(p) = 2 · pisano_predict(p)

across all three Galois branches (ramified, split, inert):

  ramified : Pell 2p           Fib 4p
  split    : Pell (p-1)/2      Fib p-1     (= 2 · (p-1)/2 for p odd)
  inert    : Pell p+1          Fib 2(p+1)

This is a *structural* identity in the 213 atomic framework — the
2× factor reflects the difference in matrix normalisation:

  Pell:       [[2, 1], [1, 1]]   tr=3, det=1, disc=5
  Fibonacci:  [[1, 1], [1, 0]]   tr=1, det=-1, disc=5

Both have discriminant 5; both fire the same Legendre lens; the
Fibonacci period is exactly twice the Pell period because the
characteristic polynomial of [[1,1],[1,0]] is x² - x - 1, whose
square is x⁴ - 2x³ + ... while [[2,1],[1,1]] has x² - 3x + 1, etc.
The order of the matrix in GL₂(F_p) doubles between the two cases.

Proven for all odd primes p ≥ 3.
-/

namespace E213.Math.Cohomology.Dyadic.Fib.PellRelation

open E213.Math.Cohomology.Dyadic.Legendre.V213 (legendre213)
open E213.Math.Cohomology.Dyadic.Pisano.Predictor (pisano_predict)
open E213.Math.Cohomology.Dyadic.Fib.PisanoCapstone (fib_pisano_predict)


/-- Auxiliary: predictor body as if-then-else (Pell). -/
private def pellBody (v p : Nat) : Nat :=
  if v = 0 then 2 * p else if v = 1 then (p - 1) / 2 else p + 1

/-- Auxiliary: predictor body as if-then-else (Fibonacci). -/
private def fibBody (v p : Nat) : Nat :=
  if v = 0 then 4 * p else if v = 1 then p - 1 else 2 * (p + 1)

private theorem pisano_predict_eq (p : Nat) (hp : 1 < p) :
    pisano_predict p hp = pellBody (legendre213 5 p hp).val p := rfl

private theorem fib_pisano_predict_eq (p : Nat) (hp : 1 < p) :
    fib_pisano_predict p hp = fibBody (legendre213 5 p hp).val p := rfl

private theorem fib_eq_two_pell_body
    (v p : Nat) (hv : v < 3) (hodd : p % 2 = 1) :
    fibBody v p = 2 * pellBody v p := by
  match v, hv with
  | 0, _ => show 4 * p = 2 * (2 * p); omega
  | 1, _ => show p - 1 = 2 * ((p - 1) / 2); omega
  | 2, _ => rfl

/-- ★★★★★★ Cross-recurrence structural identity:
    fib_pisano_predict(p) = 2 · pisano_predict(p) for all odd p ≥ 3. -/
theorem fib_predict_eq_two_pell_predict
    (p : Nat) (hp : 1 < p) (hodd : p % 2 = 1) :
    fib_pisano_predict p hp = 2 * pisano_predict p hp := by
  rw [fib_pisano_predict_eq, pisano_predict_eq]
  exact fib_eq_two_pell_body _ p (legendre213 5 p hp).isLt hodd

/-- ★★★★★ Concrete instance: predictor doubling at p = 11 (split). -/
theorem fib_pell_at_11 :
    fib_pisano_predict 11 (by decide) = 2 * pisano_predict 11 (by decide) := by
  decide

/-- ★★★★★ Concrete instance: predictor doubling at p = 7 (inert). -/
theorem fib_pell_at_7 :
    fib_pisano_predict 7 (by decide) = 2 * pisano_predict 7 (by decide) := by
  decide

/-- ★★★★★ Concrete instance: predictor doubling at p = 5 (ramified). -/
theorem fib_pell_at_5 :
    fib_pisano_predict 5 (by decide) = 2 * pisano_predict 5 (by decide) := by
  decide

end E213.Math.Cohomology.Dyadic.Fib.PellRelation
