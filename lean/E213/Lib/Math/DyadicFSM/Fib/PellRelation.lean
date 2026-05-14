import E213.Lib.Math.DyadicFSM.Legendre.Legendre
import E213.Lib.Math.DyadicFSM.Pisano.Predictor
import E213.Lib.Math.DyadicFSM.Fib.PisanoCapstone
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper

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

namespace E213.Lib.Math.DyadicFSM.Fib.PellRelation

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.DyadicFSM.Pisano.Predictor (pisano_predict)
open E213.Lib.Math.DyadicFSM.Fib.PisanoCapstone (fib_pisano_predict)


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

/-- Helper: `p - 1` is even when `p % 2 = 1`. -/
private theorem p_minus_one_mod_two {p : Nat} (hp1 : 0 < p)
    (hodd : p % 2 = 1) : (p - 1) % 2 = 0 := by
  have h1 : p % 2 = (p - 1 + 1) % 2 := by
    rw [E213.Tactic.NatHelper.sub_one_add_one (Nat.pos_iff_ne_zero.mp hp1)]
  rw [h1] at hodd
  rw [E213.Meta.Nat.AddMod213.add_mod_left (by decide : 0 < 2) (p - 1) 1] at hodd
  -- hodd : ((p - 1) % 2 + 1) % 2 = 1
  have hpm : (p - 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases Nat.lt_or_ge ((p - 1) % 2) 1 with h0 | h1'
  · exact Nat.le_zero.mp (Nat.le_of_lt_succ h0)
  · have : (p - 1) % 2 = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hpm) h1'
    rw [this] at hodd; exact absurd hodd (by decide)

private theorem fib_eq_two_pell_body
    (v p : Nat) (hv : v < 3) (hp : 1 < p) (hodd : p % 2 = 1) :
    fibBody v p = 2 * pellBody v p := by
  rcases Nat.lt_or_ge v 1 with hv0 | hv1
  · -- v = 0
    have hv_eq : v = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ hv0)
    subst hv_eq
    show 4 * p = 2 * (2 * p)
    rw [show (4 : Nat) = 2 * 2 from rfl, E213.Tactic.NatHelper.mul_assoc]
  · rcases Nat.lt_or_ge v 2 with hv1' | hv2
    · -- v = 1
      have hv_eq : v = 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ hv1') hv1
      subst hv_eq
      show p - 1 = 2 * ((p - 1) / 2)
      have hpos : 0 < p := Nat.lt_of_succ_lt hp
      have hmod0 : (p - 1) % 2 = 0 := p_minus_one_mod_two hpos hodd
      have h1 : 2 * ((p - 1) / 2) + (p - 1) % 2 = p - 1 :=
        E213.Meta.Nat.AddMod213.div_add_mod (p - 1) 2
      rw [hmod0, Nat.add_zero] at h1
      exact h1.symm
    · -- v = 2
      have hv_eq : v = 2 :=
        Nat.le_antisymm (Nat.le_of_lt_succ hv) hv2
      subst hv_eq
      rfl

/-- ★★★★★★ Cross-recurrence structural identity:
    fib_pisano_predict(p) = 2 · pisano_predict(p) for all odd p ≥ 3.
    STRICT ∅-AXIOM. -/
theorem fib_predict_eq_two_pell_predict
    (p : Nat) (hp : 1 < p) (hodd : p % 2 = 1) :
    fib_pisano_predict p hp = 2 * pisano_predict p hp := by
  rw [fib_pisano_predict_eq, pisano_predict_eq]
  exact fib_eq_two_pell_body _ p (legendre213 5 p hp).isLt hp hodd

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

end E213.Lib.Math.DyadicFSM.Fib.PellRelation
