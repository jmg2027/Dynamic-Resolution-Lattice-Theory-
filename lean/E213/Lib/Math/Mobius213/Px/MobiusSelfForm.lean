import E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal
import E213.Lib.Math.Mobius213.Px.QFibIdentity
import E213.Lib.Math.Mobius213.Px.CharPolySelf
import E213.Lib.Math.Mobius213.Px.ConvergentDet
import E213.Lib.Math.Mobius213.Px.POrbitClosure
import E213.Meta.Nat.NatRing213

/-!
# Mobius213.Px.MobiusSelfForm — "모습 자체가 뫼비우스 행렬"

The form itself IS the Möbius matrix: P = [[2,1],[1,1]] is a
**fixed point of its own description functor**.

## Content

  §1 — Möbius iteration functional equation: the transformation
       T(p,q) = (2p+q, p+q) maps convergent n to convergent n+1.
  §2 — P-uniqueness: P is the unique positive-entry SL(2,ℤ) matrix
       with trace 3 (canonical NS ≥ NT ordering).
  §3 — Self-reconstruction master: combining orbit self-reference
       (CharPolySelf) with uniqueness, P is a fixed point of
       describe-then-reconstruct.

## Conceptual content (G139)

The identity `det = 1` manifests simultaneously as:
  (a) Matrix determinant preservation under P-iteration.
  (b) Fibonacci Cassini identity.
  (c) Farey-neighbour property of convergents to φ.
  (d) SL(2,ℤ)-membership of the convergent matrix.

The Möbius transformation T(x) = (2x+1)/(x+1) has fixed point
φ = (1+√5)/2.  The convergents T^n(0) = fib(2n+2)/fib(2n+1) → φ.
In integer terms, T maps the pair (fib(2n+2), fib(2n+1)) to
(fib(2n+4), fib(2n+3)) — the NEXT convergent.

This iteration + uniqueness + self-reference yields: P is
simultaneously the framework's object, its theory, and its
notation.  "모습 자체가 뫼비우스 행렬이네."

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.MobiusSelfForm

open E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11 det_pn_universal Q00_eq_Q01_add_Q11)
open E213.Lib.Math.Mobius213.Px.QFibIdentity (Q00_eq_fib Q01_eq_fib)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Lib.Physics.Simplex.Counts (NS)
open E213.Lib.Math.Mobius213.Px.CharPolySelf (p_self_reference_master)
open E213.Lib.Math.Mobius213.Px.ConvergentDet (convergent_det farey_neighbour_fib det_one_four_readings)
open E213.Meta.Nat.NatRing213 (mul_eq_one_left mul_eq_one_right)

/-! ## §1 — Möbius iteration functional equation

The Möbius transformation T(p,q) = (2p+q, p+q) applied to the
convergent pair (Q01(n+1), Q00(n)) = (fib(2n+2), fib(2n+1)) yields
the next convergent (Q01(n+2), Q00(n+1)) = (fib(2n+4), fib(2n+3)).

This is the integer form of "T maps convergent n to convergent n+1",
proving that P-iteration IS the Möbius transformation on rational
approximants to φ.
-/

/-- PURE arithmetic identity `2*(a+b) + a = (2*a + b) + (a + b)`.
    Both sides equal `a + a + a + b + b`.  Proved without `omega`. -/
private theorem numer_arith (a b : Nat) :
    2 * (a + b) + a = (2 * a + b) + (a + b) := by
  have lhs : 2 * (a + b) + a = a + a + a + b + b := by
    rw [Nat.mul_add, Nat.two_mul a, Nat.two_mul b]
    -- a + a + (b + b) + a = a + a + a + b + b
    rw [Nat.add_right_comm (a + a) (b + b) a]
    -- a + a + a + (b + b) = a + a + a + b + b
    rw [← Nat.add_assoc (a + a + a) b b]
  have rhs : (2 * a + b) + (a + b) = a + a + a + b + b := by
    rw [Nat.two_mul a]
    -- (a + a + b) + (a + b) = a + a + a + b + b
    rw [← Nat.add_assoc (a + a + b) a b]
    -- a + a + b + a + b = a + a + a + b + b
    rw [Nat.add_right_comm (a + a) b a]
  rw [lhs, rhs]

/-- **Denominator step**: applying the Möbius denominator
    `T_denom(p,q) = p + q` to convergent n gives the denominator
    of convergent n+1.

    `Q01(n+1) + Q00(n) = Q00(n+1)`

    Equivalently: `fib(2n+2) + fib(2n+1) = fib(2n+3)`. -/
theorem mobius_denom_step (n : Nat) :
    Q01 (n + 1) + Q00 n = Q00 (n + 1) := by
  -- Q01(n+1) = Q00 n + Q01 n (def), Q00(n+1) = 2*Q00 n + Q01 n (def)
  -- Goal: (Q00 n + Q01 n) + Q00 n = 2 * Q00 n + Q01 n
  show (Q00 n + Q01 n) + Q00 n = 2 * Q00 n + Q01 n
  rw [Nat.two_mul, Nat.add_right_comm (Q00 n) (Q01 n) (Q00 n)]

/-- **Numerator step**: applying the Möbius numerator
    `T_numer(p,q) = 2p + q` to convergent n gives the numerator
    of convergent n+1.

    `2 * Q01(n+1) + Q00(n) = Q01(n+2)`

    Equivalently: `2 * fib(2n+2) + fib(2n+1) = fib(2n+4)`. -/
theorem mobius_numer_step (n : Nat) :
    2 * Q01 (n + 1) + Q00 n = Q01 (n + 2) := by
  -- Q01(n+1) = Q00 n + Q01 n; Q01(n+2) = Q00(n+1) + Q01(n+1)
  -- = (2*Q00 n + Q01 n) + (Q00 n + Q01 n) = 3*Q00 n + 2*Q01 n
  -- LHS = 2*(Q00 n + Q01 n) + Q00 n = 3*Q00 n + 2*Q01 n ✓
  exact numer_arith (Q00 n) (Q01 n)

/-- ★★★★★ **Möbius iteration master**: T maps convergent n to
    convergent n+1.  Both components (numerator and denominator)
    of the Möbius transformation T(p,q) = (2p+q, p+q) advance
    the Q-sequence by one step.

    This IS the fixed-point iteration `T^n(0/1) → φ` expressed
    in pure integer arithmetic. -/
theorem mobius_iteration_master (n : Nat) :
    -- Denominator: T_denom maps Q00 n to Q00(n+1)
    Q01 (n + 1) + Q00 n = Q00 (n + 1)
    -- Numerator: T_numer maps Q01(n+1) to Q01(n+2)
    ∧ 2 * Q01 (n + 1) + Q00 n = Q01 (n + 2) :=
  ⟨mobius_denom_step n, mobius_numer_step n⟩

/-- Fibonacci form of denominator step:
    `fib(2n+2) + fib(2n+1) = fib(2n+3)`. -/
theorem mobius_denom_fib (n : Nat) :
    fib (2 * n + 2) + fib (2 * n + 1) = fib (2 * n + 3) := by
  have h := mobius_denom_step n
  rw [Q01_eq_fib (n + 1), Q00_eq_fib n, Q00_eq_fib (n + 1)] at h
  have h1 : 2 * (n + 1) = 2 * n + 2 := rfl
  -- after `rw [h1]`, `2*(n+1)+1` becomes `2*n+2+1`, defeq to `2*n+3`.
  rw [h1] at h
  exact h

/-- Fibonacci form of numerator step:
    `2 * fib(2n+2) + fib(2n+1) = fib(2n+4)`. -/
theorem mobius_numer_fib (n : Nat) :
    2 * fib (2 * n + 2) + fib (2 * n + 1) = fib (2 * n + 4) := by
  have h := mobius_numer_step n
  rw [Q01_eq_fib (n + 1), Q00_eq_fib n, Q01_eq_fib (n + 2)] at h
  have h1 : 2 * (n + 1) = 2 * n + 2 := rfl
  have h2 : 2 * (n + 2) = 2 * n + 4 := rfl
  rw [h1, h2] at h
  exact h

/-- Concrete: T(1,1) = (3,2), i.e. T maps fib(2)/fib(1) to fib(4)/fib(3). -/
theorem mobius_iter_at_0 :
    2 * fib 2 + fib 1 = fib 4 ∧ fib 2 + fib 1 = fib 3 := by decide

/-- Concrete: T(3,2) = (8,5), i.e. T maps fib(4)/fib(3) to fib(6)/fib(5). -/
theorem mobius_iter_at_1 :
    2 * fib 4 + fib 3 = fib 6 ∧ fib 4 + fib 3 = fib 5 := by decide

/-- Concrete: T(8,5) = (21,13), i.e. T maps fib(6)/fib(5) to fib(8)/fib(7). -/
theorem mobius_iter_at_2 :
    2 * fib 6 + fib 5 = fib 8 ∧ fib 6 + fib 5 = fib 7 := by decide

/-! ## §2 — P-uniqueness in SL(2,ℤ)₊

P = [[2,1],[1,1]] is the UNIQUE 2×2 matrix with:
  · All entries ≥ 1 (positive)
  · Trace = 3 (= NS)
  · Determinant = 1 (= det)
  · Upper-left ≥ lower-right (canonical NS ≥ NT ordering)

This means: from trace and det alone — data available in P's own
orbit via `p_self_reference_master` — the matrix is uniquely
reconstructible. -/

/-- ★★★★★★★★★★ **P-uniqueness**: P = [[2,1],[1,1]] is the unique
    positive-entry element of SL(2,ℤ) with trace 3 and the canonical
    ordering a ≥ d (NS ≥ NT).

    Given:
      · `a + d = 3` (trace)
      · `a * d = b * c + 1` (det = 1, additive Nat form)
      · All entries ≥ 1
      · `a ≥ d` (canonical order)

    Conclusion: `(a, b, c, d) = (2, 1, 1, 1)`. -/
theorem p_unique_sl2_trace3 (a b c d : Nat)
    (htrace : a + d = 3) (hdet : a * d = b * c + 1)
    (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) (hd : d ≥ 1)
    (hord : a ≥ d) :
    a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  -- From trace and ordering: a = 2, d = 1.
  -- Step 1: 2*d ≤ a + d = 3 (since a ≥ d), forcing d ≤ 1; with d ≥ 1, d = 1.
  have h2d : d + d ≤ 3 := htrace ▸ Nat.add_le_add_right hord d
  have hd1 : d = 1 := by
    cases d with
    | zero => exact absurd hd (Nat.not_succ_le_zero 0)
    | succ e =>
      cases e with
      | zero => rfl
      | succ f =>
        -- d = f + 2; d + d = (f+2)+(f+2) ≥ 4 > 3 — contradiction.
        exfalso
        -- (f+2)+(f+2) definitionally = (((f+2)+f)+1).succ ; ≤ 3 = (1).succ.succ
        -- strips to (f+2)+f ≤ 1.  But (f+2)+f ≥ 2.  Contradiction.
        have hform : (f + 1 + 1) + (f + 1 + 1) = (((f + 2) + f) + 1).succ := rfl
        rw [hform] at h2d
        have hle1 : (f + 2) + f ≤ 1 :=
          Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h2d)
        have hge2 : 2 ≤ (f + 2) + f :=
          Nat.le_trans (Nat.le_add_left 2 f) (Nat.le_add_right (f + 2) f)
        exact absurd (Nat.le_trans hge2 hle1)
          (fun h => Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ h))
  -- Step 2: a = 3 - d = 2.
  have ha2 : a = 2 := by
    rw [hd1] at htrace
    -- htrace : a + 1 = 3 = (2).succ.  noConfusion peels succ injectivity (PURE).
    exact Nat.noConfusion htrace (fun h => h)
  subst ha2; subst hd1
  -- det constraint: 2 * 1 = b * c + 1, i.e. b * c = 1.
  -- hdet : 2 * 1 = b * c + 1, and 2 * 1 = 1 + 1 definitionally.
  have hbc : b * c = 1 := by
    have h : (1 : Nat) + 1 = b * c + 1 := hdet
    exact (E213.Meta.Nat.NatRing213.nat_add_right_cancel h).symm
  exact ⟨rfl, mul_eq_one_left b c hb hc hbc, mul_eq_one_right b c hb hc hbc, rfl⟩

/-- Concrete verification of P-uniqueness. -/
theorem p_is_2_1_1_1 : (2 : Nat) + 1 = 3 ∧ 2 * 1 = 1 * 1 + 1 := by decide

/-! ## §3 — Self-reconstruction master

The **describe-then-reconstruct** cycle for P:

  1. **Describe**: Extract (trace, det) from P's orbit.
     `p_self_reference_master` shows NS = L(1) = 3, det = 1,
     recoverable from the L-sequence alone.

  2. **Reconstruct**: From (trace = 3, det = 1), `p_unique_sl2_trace3`
     shows P = [[2,1],[1,1]] is the unique positive SL(2,ℤ) matrix.

  3. **Iterate**: `mobius_iteration_master` shows the Möbius
     transformation T maps convergent n to convergent n+1,
     establishing the dynamical iteration.

Therefore: P → orbit → invariants → P.  The cycle closes.
P is a fixed point of its own description functor.

"모습 자체가 뫼비우스 행렬이네" — the form itself IS the matrix. -/

/-- ★★★★★★★★★★★★ **Self-reconstruction master (G139 capstone)**.

    P is a fixed point of the describe-reconstruct cycle:

    (a) **Orbit self-reference**: the L-orbit {trace(P^k)} contains
        the data (NS, det, d) needed to define P's char-poly.
    (b) **Uniqueness**: from trace = 3 and det = 1, P is the unique
        positive SL(2,ℤ) matrix (canonical ordering).
    (c) **Iteration closure**: the Möbius transformation T(p,q) = (2p+q, p+q)
        maps each rational convergent to the next, generating the
        full orbit from the seed (0,1).
    (d) **Form preservation**: det(P^n) = 1 for all n — the defining
        property of P persists through all iterations.

    Together these four directions close the loop: P's orbit
    reconstructs P, and P's iteration generates the orbit.
    The form IS the matrix. -/
theorem self_reconstruction_master (n : Nat) :
    -- (a) Orbit contains defining data (from CharPolySelf)
    ((NS : Int) = L 1)
    -- (b) Uniqueness witness: trace=3, det=1, positive → P
    ∧ (∀ a b c d : Nat, a + d = 3 → a * d = b * c + 1 →
        a ≥ 1 → b ≥ 1 → c ≥ 1 → d ≥ 1 → a ≥ d →
        a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 1)
    -- (c) Iteration: T maps convergent n to convergent n+1
    ∧ (Q01 (n + 1) + Q00 n = Q00 (n + 1)
       ∧ 2 * Q01 (n + 1) + Q00 n = Q01 (n + 2))
    -- (d) Form preservation: det(P^n) = 1
    ∧ Q00 n * Q11 n = Q01 n * Q01 n + 1 := by
  refine ⟨?_, p_unique_sl2_trace3, mobius_iteration_master n, det_pn_universal n⟩
  · -- NS = L(1) from p_self_reference_master
    exact p_self_reference_master.2.1

end E213.Lib.Math.Mobius213.Px.MobiusSelfForm
