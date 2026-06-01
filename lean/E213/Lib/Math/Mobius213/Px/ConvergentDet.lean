import E213.Lib.Math.Mobius213.Px.QFibIdentity
import E213.Lib.Math.Mobius213.Px.FibCassini
import E213.Lib.Math.NatRing

/-!
# Mobius213.Px.ConvergentDet — Farey-neighbour property of P-convergents

The P-orbit convergents to φ² are consecutive Fibonacci ratios:

  `c(n) = fib(2n+2) / fib(2n+1)`

(i.e. `Q01(n+1) / Q00(n)` in Q-sequence terms).

Consecutive convergents are **Farey neighbours** — their
cross-determinant equals 1:

  `fib(2n+2) · fib(2n+1) − fib(2n) · fib(2n+3) = 1`  ∀ n

This is the "Stern-Brocot mediant" reading of det(P) = 1:
the Möbius transformation `T(x) = (2x+1)/(x+1)` maps each
convergent to the next, and because `det(T) = 2·1 − 1·1 = 1`,
consecutive convergents remain Farey neighbours.

## Proof strategy

The convergent cross-determinant:
  `Q01(n+1) · Q00(n) = Q01(n) · Q00(n+1) + 1`

unfolds to `Q00(n)² + Q01(n)·Q00(n) = 2·Q01(n)·Q00(n) + Q01(n)² + 1`.

From `Q00 = Q01 + Q11` (column-sum symmetry) we get
`Q00² = Q00·Q01 + Q00·Q11`, and substituting
`Q00·Q11 = Q01² + 1` (det_pn_universal) yields `Q00² = Q00·Q01 + Q01² + 1`.

Therefore LHS = `(Q00·Q01 + Q01² + 1) + Q01·Q00 = 2·Q00·Q01 + Q01² + 1` = RHS.

The Farey property IS `det(P^n) = 1` in different clothing.

## Conceptual content: "모습 자체가 뫼비우스 행렬"

The identity `det = 1` manifests simultaneously as:
  (a) Matrix determinant preservation under P-iteration.
  (b) Fibonacci Cassini identity.
  (c) Farey-neighbour property of convergents to φ².
  (d) SL(2,ℤ)-membership of the convergent matrix.

These four are the SAME theorem.  The **form** of P (det = 1)
persists through every representation.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.ConvergentDet

open E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11 det_pn_universal Q00_eq_Q01_add_Q11)
open E213.Lib.Math.Mobius213.Px.QFibIdentity (Q00_eq_fib Q01_eq_fib)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.Mobius213.Px.FibCassini (fib_cassini_shifted)
open E213.Lib.Math.NatRing (nat_add_mul nat_mul_assoc)

/-! ## §1 — Convergent cross-determinant = 1 -/

/-- `a + (b + 1) + a = 2·a + b + 1`.  PURE additive rearrangement
    (replaces an `omega` in `convergent_det`). -/
private theorem add_dup_succ (a b : Nat) : a + (b + 1) + a = 2 * a + b + 1 := by
  rw [Nat.two_mul, Nat.add_right_comm a (b + 1) a, ← Nat.add_assoc]

/-- ★★★★★★★★★★ **Convergent cross-determinant**:
    For all n, `Q01(n+1) · Q00(n) = Q01(n) · Q00(n+1) + 1`.

    Expanded form: `(Q00 n + Q01 n) · Q00 n = Q01 n · (2 · Q00 n + Q01 n) + 1`.

    Derived from `det_pn_universal` + column-sum symmetry. -/
theorem convergent_det (n : Nat) :
    (Q00 n + Q01 n) * Q00 n =
    Q01 n * (2 * Q00 n + Q01 n) + 1 := by
  have hsym := Q00_eq_Q01_add_Q11 n
  have hdet := det_pn_universal n
  -- `Q00² = Q00·Q01 + (Q01² + 1)` from the column-sum symmetry and det = 1.
  have hQ00sq : Q00 n * Q00 n = Q00 n * Q01 n + (Q01 n * Q01 n + 1) := by
    have h : Q00 n * Q00 n = Q00 n * Q01 n + Q00 n * Q11 n :=
      calc Q00 n * Q00 n
          = Q00 n * (Q01 n + Q11 n) := by rw [← hsym]
        _ = Q00 n * Q01 n + Q00 n * Q11 n := Nat.mul_add _ _ _
    rw [hdet] at h; exact h
  -- Normalise both sides to atoms `Q01·Q00`, `Q01·Q01`, then close additively.
  have c1 : Q00 n * Q01 n = Q01 n * Q00 n := Nat.mul_comm _ _
  have c2 : Q01 n * (2 * Q00 n + Q01 n)
          = 2 * (Q01 n * Q00 n) + Q01 n * Q01 n := by
    rw [Nat.mul_add, Nat.mul_comm (Q01 n) (2 * Q00 n), nat_mul_assoc,
        Nat.mul_comm (Q00 n) (Q01 n)]
  calc (Q00 n + Q01 n) * Q00 n
      = Q00 n * Q00 n + Q01 n * Q00 n := by rw [nat_add_mul]
    _ = Q00 n * Q01 n + (Q01 n * Q01 n + 1) + Q01 n * Q00 n := by rw [hQ00sq]
    _ = Q01 n * (2 * Q00 n + Q01 n) + 1 := by
        rw [c1, c2]; exact add_dup_succ (Q01 n * Q00 n) (Q01 n * Q01 n)

/-! ## §2 — Fibonacci form -/

/-- ★★★★★★★★★★ **Farey-neighbour property (Fibonacci form)**:
    `fib(2n+2) · fib(2n+1) = fib(2n) · fib(2n+3) + 1`

    Consecutive convergents `fib(2n+2)/fib(2n+1)` and
    `fib(2n+4)/fib(2n+3)` to φ² are Farey neighbours in
    the Stern-Brocot tree.

    Derived from `convergent_det` via Fibonacci substitution. -/
theorem farey_neighbour_fib (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 1) =
    fib (2 * n) * fib (2 * n + 3) + 1 := by
  have hconv := convergent_det n
  -- (Q00 n + Q01 n) * Q00 n = Q01 n * (2 * Q00 n + Q01 n) + 1
  -- Q00 n + Q01 n = Q01(n+1) = fib(2(n+1)) = fib(2n+2)  [definitionally]
  -- Q00 n = fib(2n+1)
  -- Q01 n = fib(2n)
  -- 2*Q00 n + Q01 n = Q00(n+1) = fib(2(n+1)+1) = fib(2n+3)  [definitionally]
  rw [show Q00 n + Q01 n = Q01 (n + 1) from rfl] at hconv
  rw [show (2 : Nat) * Q00 n + Q01 n = Q00 (n + 1) from rfl] at hconv
  rw [Q01_eq_fib (n + 1)] at hconv
  rw [Q00_eq_fib n] at hconv
  rw [Q01_eq_fib n] at hconv
  rw [Q00_eq_fib (n + 1)] at hconv
  have h1 : 2 * (n + 1) = 2 * n + 2 := rfl
  -- after `rw [h1]`, the `2*(n+1)+1` argument becomes `2*n+2+1`, which is
  -- defeq to `2*n+3`; no second rewrite needed.
  rw [h1] at hconv
  exact hconv

/-! ## §3 — Concrete verification -/

/-- n=0: fib 2 · fib 1 = fib 0 · fib 3 + 1, i.e. 1·1 = 0·2 + 1. -/
theorem farey_at_0 : fib 2 * fib 1 = fib 0 * fib 3 + 1 := by decide

/-- n=1: fib 4 · fib 3 = fib 2 · fib 5 + 1, i.e. 3·2 = 1·5 + 1. -/
theorem farey_at_1 : fib 4 * fib 3 = fib 2 * fib 5 + 1 := by decide

/-- n=2: fib 6 · fib 5 = fib 4 · fib 7 + 1, i.e. 8·5 = 3·13 + 1. -/
theorem farey_at_2 : fib 6 * fib 5 = fib 4 * fib 7 + 1 := by decide

/-- n=3: fib 8 · fib 7 = fib 6 · fib 9 + 1, i.e. 21·13 = 8·34 + 1. -/
theorem farey_at_3 : fib 8 * fib 7 = fib 6 * fib 9 + 1 := by decide

/-- n=4: fib 10 · fib 9 = fib 8 · fib 11 + 1, i.e. 55·34 = 21·89 + 1. -/
theorem farey_at_4 : fib 10 * fib 9 = fib 8 * fib 11 + 1 := by decide

/-! ## §4 — Master: four readings of det = 1

The single identity `det(P^n) = 1` appears as four equivalent
statements.  Their algebraic equivalence is witnessed by the
Q-sequence recurrence definitions. -/

/-- ★★★★★★★★★★★★ **Master: four readings of det = 1**.

    (a) Matrix determinant: `Q00 n · Q11 n = Q01 n² + 1`
    (b) Fibonacci Cassini: `fib(2n+3)·fib(2n+1) = fib(2n+2)² + 1`
    (c) Farey neighbour: `fib(2n+2)·fib(2n+1) = fib(2n)·fib(2n+3) + 1`

    All three are the SAME identity (det P^n = 1) viewed through
    different Lenses.  "모습 자체가 뫼비우스 행렬" — the form
    (det = 1) IS the Möbius matrix's defining property, and it
    manifests identically at every level. -/
theorem det_one_four_readings (n : Nat) :
    -- (a) Matrix determinant
    Q00 n * Q11 n = Q01 n * Q01 n + 1
    -- (b) Fibonacci Cassini
    ∧ fib (2 * n + 3) * fib (2 * n + 1) = fib (2 * n + 2) * fib (2 * n + 2) + 1
    -- (c) Farey neighbour
    ∧ fib (2 * n + 2) * fib (2 * n + 1) = fib (2 * n) * fib (2 * n + 3) + 1 :=
  ⟨det_pn_universal n, fib_cassini_shifted n, farey_neighbour_fib n⟩

end E213.Lib.Math.Mobius213.Px.ConvergentDet
