import E213.Lib.Physics.Simplex.Counts
import E213.Term.Tactic.Nat213

/-!
# G14 — Binom symmetry: `C(n, k) = C(n, n − k)` (213-native ∅-axiom)

213's `binom` (defined in `Lib/Physics/Simplex/Counts.lean` via
Pascal recursion) admits the standard symmetry

  binom n k = binom n (n − k)   for k ≤ n.

This file provides the inductive proof in 213-native form, using
only:
  · Pascal recursion (rfl from `binom`'s definition)
  · `Nat.succ_sub_succ_eq_sub`, `Nat.add_comm`, `Nat.le_*`
    (Lean-core PURE lemmas)
  · `E213.Tactic.Nat213.{sub_pos_of_lt, sub_add_cancel}`
    (213-native replacements for the propext-tainted Lean-core
    forms)

## Why G14

Closes the open prerequisite for the **inductive** form of the
T²ⁿ pattern theorem `signature(H^n; T²ⁿ) = (½·C(2n, n), ½·C(2n, n))`
across all `n`.  Specifically: with binom symmetry in hand, we
can prove `C(2n, n) = 2·C(2n−1, n−1)` for `n ≥ 1`, hence
`C(2n, n)` is even.  With evenness, the parametric instance
`T2n_blocks (n : Nat) (hn : 1 ≤ n) : BalancedSignatureData` is
constructable, and the master A theorem extends to all `n`.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.NatHelpers.BinomSymm

open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1 — Auxiliary: `binom n k = 0` for `n < k` -/

/-- Out-of-range: `binom n k = 0` whenever `n < k`. -/
theorem binom_too_big : ∀ {n k : Nat}, n < k → binom n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _+1, _ => rfl
  | _+1, 0, h => absurd h (Nat.not_lt_zero _)
  | n+1, k+1, h => by
    show binom n k + binom n (k+1) = 0
    have h1 : n < k := Nat.lt_of_succ_lt_succ h
    have h2 : n < k + 1 := Nat.lt_succ_of_lt h1
    rw [binom_too_big h1, binom_too_big h2]

/-! ## §2 — Diagonal: `binom n n = 1` -/

/-- Diagonal: `binom n n = 1`. -/
theorem binom_diag : ∀ n : Nat, binom n n = 1
  | 0 => rfl
  | n+1 => by
    show binom n n + binom n (n+1) = 1
    rw [binom_diag n, binom_too_big (Nat.lt_succ_self n)]

/-! ## §3 — Symmetry: `binom n k = binom n (n − k)` for `k ≤ n` -/

/-- ★★★★★ Binom symmetry — STRICT ∅-AXIOM.

    `binom n k = binom n (n − k)` whenever `k ≤ n`.

    Inductive proof on the pattern `n+1, k+1`:
      · Pascal recursion expands LHS and RHS by definition.
      · Inductive hypothesis on `(n, k)` and `(n, k+1)` rewrites
        each summand.
      · Boundary case `k+1 = n+1` reduces to `binom_diag` + zero.

    Uses 213-native `Nat213.sub_pos_of_lt` and `Nat213.sub_add_cancel`
    to avoid Lean-core propext on the Nat-subtraction lemmas. -/
theorem binom_symm : ∀ {n k : Nat}, k ≤ n → binom n k = binom n (n - k)
  | 0, 0, _ => rfl
  | 0, k+1, h => absurd h (Nat.not_succ_le_zero k)
  | n+1, 0, _ => by
    show 1 = binom (n+1) (n+1)
    rw [binom_diag]
  | n+1, k+1, h => by
    have h_outer : (n + 1) - (k + 1) = n - k := Nat.succ_sub_succ_eq_sub n k
    rw [h_outer]
    by_cases hkn : k + 1 ≤ n
    · have hk : k ≤ n := Nat.le_of_succ_le hkn
      show binom n k + binom n (k + 1) = binom (n + 1) (n - k)
      rw [binom_symm hk, binom_symm hkn]
      have h_subsucc : n - (k + 1) = (n - k) - 1 := rfl
      rw [h_subsucc]
      have hge : 1 ≤ n - k := E213.Tactic.Nat213.sub_pos_of_lt hkn
      obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 :=
        ⟨(n - k) - 1, (E213.Tactic.Nat213.sub_add_cancel hge).symm⟩
      rw [hm]
      show binom n (m + 1) + binom n m = binom n m + binom n (m + 1)
      exact Nat.add_comm _ _
    · have hk_eq : k = n :=
        Nat.le_antisymm (Nat.le_of_succ_le_succ h) (Nat.le_of_not_lt hkn)
      rw [hk_eq, binom_diag, Nat.sub_self]
      rfl

end E213.Lib.Math.NatHelpers.BinomSymm

namespace E213.Lib.Math.NatHelpers.BinomSymm

open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §4 — Central binomial is even for n ≥ 1 -/

/-- ★★★★★ `C(2n+2, n+1) = 2 · C(2n+1, n+1)` for all `n`.
    STRICT ∅-AXIOM.

    Proof:
      C(2n+2, n+1) = C(2n+1, n) + C(2n+1, n+1)         (Pascal)
                   = C(2n+1, n+1) + C(2n+1, n+1)        (binom_symm: (2n+1)−n = n+1)
                   = 2·C(2n+1, n+1).
-/
theorem central_binom_is_double (n : Nat) :
    binom (2 * (n + 1)) (n + 1) = 2 * binom (2 * n + 1) (n + 1) := by
  -- Step 1: rewrite 2*(n+1) = (2n+1)+1 (rfl from Nat.mul def)
  have h_two_succ : 2 * (n + 1) = (2 * n + 1) + 1 := by
    show 2 * n + 2 = (2 * n + 1) + 1
    rfl
  -- Step 2: 2*n + 1 = n + (n + 1) (via two_mul + add_assoc + add_comm)
  have h_2n1 : 2 * n + 1 = n + (n + 1) := by
    have h1 : 2 * n = n + n := E213.Tactic.Nat213.two_mul n
    rw [h1]
    -- (n + n) + 1 = n + (n + 1) by Nat.add_assoc
    exact Nat.add_assoc n n 1
  -- Step 3: (2n+1) − n = n + 1
  have h_sub : 2 * n + 1 - n = n + 1 := by
    rw [h_2n1]
    -- Goal: n + (n + 1) - n = n + 1
    -- Use add_sub_add_left k (b) (0): (k + b) - (k + 0) = b - 0 = b.
    -- Or simpler: n + (n+1) - n = (n+1) by add comm + add_sub_cancel_right.
    rw [Nat.add_comm n (n + 1)]
    exact E213.Tactic.Nat213.add_sub_cancel_right (n + 1) n
  -- Step 4: n ≤ 2n + 1
  have hk_le : n ≤ 2 * n + 1 := by
    rw [h_2n1]
    exact Nat.le_add_right n (n + 1)
  -- Now apply binom_symm + double
  rw [h_two_succ]
  show binom (2 * n + 1) n + binom (2 * n + 1) (n + 1)
        = 2 * binom (2 * n + 1) (n + 1)
  have h_symm : binom (2 * n + 1) n = binom (2 * n + 1) (n + 1) := by
    rw [binom_symm hk_le, h_sub]
  rw [h_symm]
  exact (E213.Tactic.Nat213.two_mul (binom (2 * n + 1) (n + 1))).symm

end E213.Lib.Math.NatHelpers.BinomSymm
