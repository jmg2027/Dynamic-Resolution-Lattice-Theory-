import E213.Lib.Math.NatRing

/-!
# Mobius213.Px.PnFibonacciUniversal — det(P^n) = 1 at every n (PURE)

`PnFibonacci.lean` verifies `det(P^n) = P00(n) · P11(n) − P01(n)² = 1`
at concrete n = 0..5.  This file lifts to ∀ n using the 213-PURE
`NatRing` ring toolkit.

## Statement (Nat-additive form)

For every `n : Nat`:
  `Q00(n) · Q11(n) = Q01(n)² + 1`

where `Q00, Q01, Q11 : Nat → Nat` are the entries of `P^n` defined
via the **1-step matrix recurrence** `P^(n+1) = P^n · P`:

  · `Q00(0) = 1, Q00(n+1) = 2·Q00(n) + Q01(n)`
  · `Q01(0) = 0, Q01(n+1) = Q00(n) + Q01(n)`
  · `Q11(0) = 1, Q11(n+1) = Q00(n)`         (from symmetry of P^n)

These reproduce the values of `PnFibonacci.{P00, P01, P11}` at
each concrete `n`, but the 1-step form avoids Nat subtraction
and lets the universal Cassini step proceed by direct algebraic
manipulation using the PURE Nat ring tools.

## Proof outline

  · §1 — Q-sequence definitions + concrete agreement with P-sequences.
  · §2 — Auxiliary: `Q00(n) = Q01(n) + Q11(n)` (symmetry of P^n).
  · §3 — Cassini-∀n: `Q00 n · Q11 n = Q01 n ² + 1`.

Inductive step uses the PURE ring tools `nat_mul_assoc`,
`nat_add_mul`, `nat_add_right_cancel`, and the IH.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal

open E213.Lib.Math.NatRing

/-! ## §1 — Q sequence: 1-step matrix entries of P^n -/

mutual
  /-- Top-left entry of P^n (= fib(2n+1)). -/
  def Q00 : Nat → Nat
    | 0     => 1
    | n + 1 => 2 * Q00 n + Q01 n
  /-- Off-diagonal entry of P^n (= fib(2n)). -/
  def Q01 : Nat → Nat
    | 0     => 0
    | n + 1 => Q00 n + Q01 n
end

/-- Bottom-right entry of P^n.  Definitionally `Q11(n+1) = Q00 n`,
    matching the symmetry of P^n.  Base case `Q11 0 = 1`. -/
def Q11 : Nat → Nat
  | 0     => 1
  | n + 1 => Q00 n

theorem Q00_0 : Q00 0 = 1 := rfl
theorem Q00_1 : Q00 1 = 2 := rfl
theorem Q00_2 : Q00 2 = 5 := rfl
theorem Q00_3 : Q00 3 = 13 := rfl
theorem Q01_0 : Q01 0 = 0 := rfl
theorem Q01_1 : Q01 1 = 1 := rfl
theorem Q01_2 : Q01 2 = 3 := rfl
theorem Q11_0 : Q11 0 = 1 := rfl
theorem Q11_1 : Q11 1 = 1 := rfl
theorem Q11_2 : Q11 2 = 2 := rfl

/-! ## §2 — Symmetry: Q00(n) = Q01(n) + Q11(n) -/

/-- ★ **Matrix symmetry**: `P^n` is symmetric (since P is), so
    `(P^n)_{0,0} = (P^n)_{0,1} + (P^n)_{1,1}`?  Actually the
    correct relation is `Q00 = Q01 + Q11` derived from the matrix
    structure `P^n = P^(n-1) · P` and the symmetry of P^(n-1). -/
theorem Q00_eq_Q01_add_Q11 : ∀ n : Nat, Q00 n = Q01 n + Q11 n
  | 0 => by decide
  | n + 1 => by
    have ih := Q00_eq_Q01_add_Q11 n
    -- Goal: Q00 (n+1) = Q01 (n+1) + Q11 (n+1)
    show 2 * Q00 n + Q01 n = (Q00 n + Q01 n) + Q00 n
    rw [two_mul_eq]
    -- Goal: Q00 n + Q00 n + Q01 n = Q00 n + Q01 n + Q00 n
    rw [Nat.add_right_comm (Q00 n) (Q00 n) (Q01 n)]

/-! ## §3 — IH-driven helper toward Cassini-∀n -/

/-- ★ **Polynomial helper from IH**: from `Q00 k · Q11 k = Q01 k² + 1`
    (the Cassini IH) and `Q00 k = Q01 k + Q11 k` (the symmetry),
    derive `Q00 k · Q00 k = Q00 k · Q01 k + (Q01 k² + 1)`.

    Proof: `Q00² = Q00·(Q01 + Q11) = Q00·Q01 + Q00·Q11
                                   = Q00·Q01 + (Q01² + 1)` (IH).

    This is the **key non-trivial inductive step** for
    `det(P^n) = 1`.  The remaining work to close `det_pn_universal`
    is an additive-commutative normalisation of the 4-monomial
    expansion of `(a + b)² + 1` vs `(2a + b)·a` after substituting
    this helper — a `nat_ring`-style normalisation step which is
    left for a future `Nat`-ring decision procedure (a small AC
    normaliser would suffice). -/
theorem Q00_sq_via_ih (k : Nat)
    (ih : Q00 k * Q11 k = Q01 k * Q01 k + 1) :
    Q00 k * Q00 k = Q00 k * Q01 k + (Q01 k * Q01 k + 1) := by
  have hsym := Q00_eq_Q01_add_Q11 k
  have step1 : Q00 k * Q00 k = Q00 k * (Q01 k + Q11 k) := by rw [← hsym]
  rw [step1, Nat.mul_add, ih]

/-! ## §4 — Cassini-∀n closure -/

/-- ★★★★★★★★★★ **`det(P^n) = 1` at every n (PURE Nat-additive)**.

    For every `n : Nat`:
      `Q00 n · Q11 n = Q01 n² + 1`

    The universal lift of `PnFibonacci.det_Pn_0..5` to ∀n via the
    PURE Nat ring toolkit (`NatRing`) — Fibonacci Cassini at even
    index.

    Inductive step: substitute `Q00² → Q00·Q01 + Q01² + 1` (via
    `Q00_sq_via_ih`) once into the expanded LHS, then close by
    additive-commutative normalisation. -/
theorem det_pn_universal (n : Nat) :
    Q00 n * Q11 n = Q01 n * Q01 n + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
    have hexp := Q00_sq_via_ih k ih
    -- Goal unfolds to: (2·Q00 + Q01)·Q00 = (Q00 + Q01)² + 1
    show (2 * Q00 k + Q01 k) * Q00 k = (Q00 k + Q01 k) * (Q00 k + Q01 k) + 1
    -- Expand LHS: 2·Q00·Q00 + Q01·Q00 = Q00·Q00 + Q00·Q00 + Q01·Q00
    rw [nat_add_mul, two_mul_eq, nat_add_mul]
    -- Expand RHS: (Q00 + Q01)(Q00 + Q01) + 1
    --           = Q00·Q00 + Q00·Q01 + Q01·Q00 + Q01·Q01 + 1
    rw [Nat.mul_add, nat_add_mul, nat_add_mul]
    -- Now substitute hexp into the SECOND Q00·Q00 on LHS using
    -- a positional show + congr chain.
    rw [Nat.add_assoc (Q00 k * Q00 k) (Q00 k * Q00 k) (Q01 k * Q00 k)]
    rw [show Q00 k * Q00 k + (Q00 k * Q00 k + Q01 k * Q00 k)
            = Q00 k * Q00 k +
              ((Q00 k * Q01 k + (Q01 k * Q01 k + 1)) + Q01 k * Q00 k)
        from by rw [hexp]]
    -- Now Q00·Q00 appears once on the LHS.  Rearrange both sides to
    -- expose matching sums.
    rw [Nat.mul_comm (Q01 k) (Q00 k)]
    -- LHS = Q00² + (Q00·Q01 + (Q01² + 1) + Q00·Q01)
    -- RHS = Q00·Q00 + Q00·Q01 + (Q00·Q01 + Q01·Q01) + 1
    -- Both have multiset {Q00², Q00·Q01 (×2), Q01², 1}.  AC.
    rw [← Nat.add_assoc, ← Nat.add_assoc]
    -- LHS = Q00² + Q00·Q01 + (Q01² + 1) + Q00·Q01
    -- RHS = Q00² + Q00·Q01 + Q00·Q01 + Q01² + 1
    rw [Nat.add_right_comm _ (Q01 k * Q01 k + 1) _]
    -- LHS = Q00² + Q00·Q01 + Q00·Q01 + (Q01² + 1)
    rw [← Nat.add_assoc _ (Q01 k * Q01 k) 1]
    -- Final RHS normalization: ungroup (Q00·Q01 + Q01²) on RHS
    rw [← Nat.add_assoc (Q00 k * Q00 k + Q00 k * Q01 k)
                         (Q00 k * Q01 k) (Q01 k * Q01 k)]

end E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal
