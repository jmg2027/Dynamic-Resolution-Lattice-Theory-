import E213.Lib.Math.DyadicFSM.PhiMod5
/-!
# Pell ↔ Fibonacci bridge (mod p) — G119 Phase 3.2 reduction

The classical identity `U_k = F_{2k}` (where `U_k` is the Pell number
satisfying `U_{k+1} = 3·U_k - U_{k-1}` and `F_n` is the standard
Fibonacci number) reduces the Pell matrix coefficient recurrence
to a fact about Fibonacci numbers at even indices.

For the (1, 1) orbit of `M = [[2, 1], [1, 1]]`:

  `pellCoeff p hp k = (F_{2k} mod p,  (p - F_{2k-2}) mod p)`
                                   (for k ≥ 1; `pellCoeff p hp 0 = (0, 1)`)

So `pellCoeff p hp N = (0, 1)` iff
  `F_{2N} ≡ 0 mod p`  AND  `F_{2N-2} ≡ -1 mod p`.

For Phase 3.2 (split case, `N = (p-1)/2`), this becomes:
  `F_{p-1} ≡ 0 mod p`  AND  `F_{p-3} ≡ -1 mod p`,
which is the classical Fibonacci-Pisano condition at split primes.

This file:
  · Defines `fibFst k := (fibLike k).1` (convenience accessor).
  · Proves `fibFst_recur` (standard Fibonacci recurrence).
  · Proves `fibFst_pell_recur` (the even-index identity
    `F_{2k+4} + F_{2k} = 3·F_{2k+2}` — the Pell recurrence in additive
    Nat form).
  · Smoke-verifies Phase 3.2 fibLike conditions at split primes
    `p ∈ {11, 19, 29}`.

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.PellFibBridge

open E213.Lib.Math.DyadicFSM.PhiMod5 (fibLike)
open E213.Tactic.NatHelper (add_mul)

/-- First component of `fibLike k` — the k-th Fibonacci number. -/
def fibFst (k : Nat) : Nat := (fibLike k).1

/-- Second component of `fibLike k` — `F_{k-1}` for k ≥ 1, and 1 for k=0
    (Fibonacci convention `F_{-1} = 1` extended backward). -/
def fibSnd (k : Nat) : Nat := (fibLike k).2

/-- Definitional: `(fibLike (k+1)).1 = (fibLike k).1 + (fibLike k).2`. -/
theorem fibLike_succ_fst (k : Nat) :
    (fibLike (k + 1)).1 = (fibLike k).1 + (fibLike k).2 := rfl

/-- Definitional: `(fibLike (k+1)).2 = (fibLike k).1`. -/
theorem fibLike_succ_snd (k : Nat) :
    (fibLike (k + 1)).2 = (fibLike k).1 := rfl

/-- ★ **Fibonacci recurrence**: `F_{k+2} = F_{k+1} + F_k`.  PURE. -/
theorem fibFst_recur (k : Nat) :
    fibFst (k + 2) = fibFst (k + 1) + fibFst k := by
  show (fibLike (k + 2)).1 = (fibLike (k + 1)).1 + (fibLike k).1
  rw [fibLike_succ_fst (k + 1), fibLike_succ_snd k]

/-- Smoke: first few Fibonacci values. -/
theorem fibFst_table :
    fibFst 0 = 0 ∧ fibFst 1 = 1 ∧ fibFst 2 = 1 ∧ fibFst 3 = 2
    ∧ fibFst 4 = 3 ∧ fibFst 5 = 5 ∧ fibFst 6 = 8 ∧ fibFst 7 = 13
    ∧ fibFst 8 = 21 ∧ fibFst 9 = 34 ∧ fibFst 10 = 55 := by decide

/-- ★ **Pell-like recurrence on even-index Fibonacci**:
    `F_{2k+4} + F_{2k} = 3·F_{2k+2}` — the Pell recurrence
    in additive Nat form (avoids Nat subtraction).

    Algebraic derivation:
      F_{2k+4}          = F_{2k+3} + F_{2k+2}                [Fibonacci]
                        = (F_{2k+2} + F_{2k+1}) + F_{2k+2}   [Fibonacci]
                        = 2·F_{2k+2} + F_{2k+1}
      F_{2k+4} + F_{2k} = 2·F_{2k+2} + (F_{2k+1} + F_{2k})
                        = 2·F_{2k+2} + F_{2k+2}              [Fibonacci]
                        = 3·F_{2k+2}.
    PURE. -/
theorem fibFst_pell_recur (k : Nat) :
    fibFst (2*k + 4) + fibFst (2*k) = 3 * fibFst (2*k + 2) := by
  have h1 : fibFst (2*k + 4) = fibFst (2*k + 3) + fibFst (2*k + 2) :=
    fibFst_recur (2*k + 2)
  have h2 : fibFst (2*k + 3) = fibFst (2*k + 2) + fibFst (2*k + 1) :=
    fibFst_recur (2*k + 1)
  have h3 : fibFst (2*k + 2) = fibFst (2*k + 1) + fibFst (2*k) :=
    fibFst_recur (2*k)
  rw [h1, h2]
  -- Goal: (F_{2k+2} + F_{2k+1}) + F_{2k+2} + F_{2k} = 3 * F_{2k+2}
  -- Rearrange: (F_{2k+2}) + (F_{2k+2}) + (F_{2k+1} + F_{2k}) = 3 * F_{2k+2}
  rw [Nat.add_assoc (fibFst (2*k + 2) + fibFst (2*k + 1)) (fibFst (2*k + 2)) (fibFst (2*k))]
  -- (F_{2k+2} + F_{2k+1}) + (F_{2k+2} + F_{2k}) = 3 * F_{2k+2}
  rw [Nat.add_assoc (fibFst (2*k + 2)) (fibFst (2*k + 1)) (fibFst (2*k + 2) + fibFst (2*k))]
  -- F_{2k+2} + (F_{2k+1} + (F_{2k+2} + F_{2k})) = 3 * F_{2k+2}
  rw [show fibFst (2*k + 1) + (fibFst (2*k + 2) + fibFst (2*k))
        = fibFst (2*k + 2) + (fibFst (2*k + 1) + fibFst (2*k)) by
      rw [← Nat.add_assoc, Nat.add_comm (fibFst (2*k + 1)) (fibFst (2*k + 2)),
          Nat.add_assoc]]
  -- F_{2k+2} + (F_{2k+2} + (F_{2k+1} + F_{2k})) = 3 * F_{2k+2}
  rw [← h3]
  -- F_{2k+2} + (F_{2k+2} + F_{2k+2}) = 3 * F_{2k+2}
  show fibFst (2*k + 2) + (fibFst (2*k + 2) + fibFst (2*k + 2)) = 3 * fibFst (2*k + 2)
  rw [show 3 * fibFst (2*k + 2) = fibFst (2*k + 2) + fibFst (2*k + 2) + fibFst (2*k + 2) by
        rw [show (3 : Nat) = 1 + 1 + 1 from rfl, add_mul, add_mul,
            Nat.one_mul]]
  rw [Nat.add_assoc]

/-! ## Phase 3.2 fibLike conditions — per-prime smokes

At split primes p (5 QR mod p), the Phase 3.2 chain requires:

  `F_{p-1} ≡ 0 (mod p)`  AND  `F_{p-3} ≡ -1 (mod p)`

The universal claim follows from FLT for phi (multi-session); each
per-prime instance is decidable.  The smokes below verify the
condition at the 11 empirically-tight split primes from the G119
Predictor23 chain. -/

/-- Smoke at p=11 (split, predict (11-1)/2 = 5):
    F_10 ≡ 0 mod 11 AND F_8 ≡ -1 mod 11. -/
theorem fib_phase_3_2_at_11 :
    fibFst 10 % 11 = 0 ∧ fibFst 8 % 11 = 10 := by decide

/-- Smoke at p=19 (split, predict 9):
    F_18 ≡ 0 mod 19 AND F_16 ≡ -1 mod 19. -/
theorem fib_phase_3_2_at_19 :
    fibFst 18 % 19 = 0 ∧ fibFst 16 % 19 = 18 := by decide

/-- Smoke at p=29 (split, predict 14):
    F_28 ≡ 0 mod 29 AND F_26 ≡ -1 mod 29.
    Note: p=29 is sub-tight (actual period 7 < predict 14), but the
    predict upper-bound still holds. -/
theorem fib_phase_3_2_at_29 :
    fibFst 28 % 29 = 0 ∧ fibFst 26 % 29 = 28 := by decide

/-- Smoke at p=31 (split, predict 15):
    F_30 ≡ 0 mod 31 AND F_28 ≡ -1 mod 31. -/
theorem fib_phase_3_2_at_31 :
    fibFst 30 % 31 = 0 ∧ fibFst 28 % 31 = 30 := by decide

/-- Smoke at p=41 (split, predict 20):
    F_40 ≡ 0 mod 41 AND F_38 ≡ -1 mod 41. -/
theorem fib_phase_3_2_at_41 :
    fibFst 40 % 41 = 0 ∧ fibFst 38 % 41 = 40 := by decide

end E213.Lib.Math.DyadicFSM.PellFibBridge
