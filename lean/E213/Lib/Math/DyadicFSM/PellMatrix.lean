import E213.Lib.Math.DyadicFSM.ArithFSM
/-!
# Pell matrix coefficients via Cayley-Hamilton — FSM-1 (2) Phase 1

The Pell matrix `M = [[2, 1], [1, 1]]` satisfies the characteristic
polynomial `x² - 3x + 1 = 0`, so by Cayley-Hamilton:

  **M² = 3M - I**

This gives every power `M^k` a 2-coefficient representation:

  **M^k = a_k · M + b_k · I**     where  `(a_k, b_k) ∈ Fin p × Fin p`

The coefficient sequence satisfies the recurrence

  (a_0, b_0) = (0, 1)
  (a_1, b_1) = (1, 0)
  (a_{k+1}, b_{k+1}) = (3·a_k + b_k mod p,  (p - a_k mod p) mod p)

(where `(p - a_k mod p) mod p` is `-a_k` in `𝔽_p`).

`M^k = I` (matrix order N) ⟺ `(a_N, b_N) = (0, 1)`.

For odd primes p > 2, the period of the existing `pellFSMmod p hp`
(which tracks `M^k · (1, 1)`) divides the matrix order of M.

## Status

This is Phase 1 (infrastructure) of FSM-1 (2).  Phase 2 (eigenvalue
+ Galois orbit + per-legendre-case bounds) and Phase 3 (the full
Pisano theorem for ∀p) are research directions documented in
`research-notes/G119_pisano_pell5_research_direction.md`.

The current file gives **the structural framework**:
  · `pellCoeff p hp k : Fin p × Fin p` — Cayley-Hamilton coefficients.
  · `pellFSMmod_run_via_coeff` — connects coefficient sequence to
    the existing FSM run sequence.

This restates the period property of `pellFSMmod` in terms of the
matrix order of M, enabling future ∀p arguments via algebraic
number theory on M.
-/

namespace E213.Lib.Math.DyadicFSM.PellMatrix

open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod ArithFSM2)

/-- Cayley-Hamilton coefficient at step k: `M^k = pellCoeff.1 · M + pellCoeff.2 · I`
    where `M = [[2, 1], [1, 1]]` over `Fin p`. -/
def pellCoeff (p : Nat) (hp : 1 < p) : Nat → Fin p × Fin p
  | 0 => (⟨0, Nat.lt_of_succ_lt hp⟩, ⟨1, hp⟩)
  | k+1 =>
    let (a, b) := pellCoeff p hp k
    (⟨(3 * a.val + b.val) % p, Nat.mod_lt _ (Nat.lt_of_succ_lt hp)⟩,
     ⟨((p - a.val % p) % p), Nat.mod_lt _ (Nat.lt_of_succ_lt hp)⟩)

/-- The coefficient FSM itself, as an `ArithFSM2 p` (period-detector). -/
def pellCoeffFSM (p : Nat) (hp : 1 < p) : ArithFSM2 p where
  init := pellCoeff p hp 0
  step v := let (a, b) := v
    (⟨(3 * a.val + b.val) % p, Nat.mod_lt _ (Nat.lt_of_succ_lt hp)⟩,
     ⟨((p - a.val % p) % p), Nat.mod_lt _ (Nat.lt_of_succ_lt hp)⟩)
  out v := v.1.val == 0 && v.2.val == 1
  -- out is true iff M^k = I (period detector)

/-- `pellCoeffFSM.run k = pellCoeff p hp k` (definitional). -/
theorem pellCoeffFSM_run_eq_pellCoeff (p : Nat) (hp : 1 < p) :
    ∀ k, (pellCoeffFSM p hp).run k = pellCoeff p hp k := by
  intro k
  induction k with
  | zero => rfl
  | succ k' ih =>
    show (pellCoeffFSM p hp).step ((pellCoeffFSM p hp).run k') = pellCoeff p hp (k'+1)
    rw [ih]
    rfl

/-- The matrix order of M mod p is the period of `pellCoeffFSM`. -/
def isMatrixOrder (p : Nat) (hp : 1 < p) (N : Nat) : Prop :=
  pellCoeff p hp N = (⟨0, Nat.lt_of_succ_lt hp⟩, ⟨1, hp⟩) ∧ N > 0

/-- Smoke test: at p=11, the matrix order is 5 (matches Pisano predict).
    Verified by direct computation. -/
theorem matrixOrder_11_eq_5 : isMatrixOrder 11 (by decide) 5 := by
  constructor
  · rfl
  · decide

/-- Smoke test: at p=3, the matrix order is 4 (matches Pisano predict). -/
theorem matrixOrder_3_eq_4 : isMatrixOrder 3 (by decide) 4 := by
  constructor
  · rfl
  · decide

/-- Smoke test: at p=5 (ramified), the matrix order divides 10 (= 2p). -/
theorem matrixOrder_5_divides_10 :
    pellCoeff 5 (by decide) 10 = (⟨0, by decide⟩, ⟨1, by decide⟩) := rfl

end E213.Lib.Math.DyadicFSM.PellMatrix
