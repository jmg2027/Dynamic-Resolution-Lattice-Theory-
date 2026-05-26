import E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal
import E213.Lib.Math.Mobius213.Px.QFibIdentity

/-!
# Mobius213.Px.FibCassini — Fibonacci Cassini identity from P^n determinant

Derives the classical **Fibonacci Cassini identity** (at even-indexed
triples) from the P^n matrix determinant:

  `fib(2n+1) · fib(2n−1) = fib(2n)² + 1`   for all n ≥ 1

This is the restriction of the general Cassini identity
`fib(m+1) · fib(m−1) − fib(m)² = (−1)^m` to even m = 2n,
where the sign is always +1.

## Proof strategy

  1. `det_pn_universal n`: Q00 n · Q11 n = Q01 n · Q01 n + 1
  2. `Q00_eq_fib n`: Q00 n = fib(2n+1)
  3. `Q01_eq_fib n`: Q01 n = fib(2n)
  4. `Q11 (n+1) = Q00 n` (by definition of Q11)
  5. Substitution gives: fib(2(n+1)+1) · fib(2n+1) = fib(2(n+1))² + 1
     i.e. fib(2n+3) · fib(2n+1) = fib(2n+2)² + 1

     Equivalently, using det at n directly:
     Q00 n · Q11 n = Q01 n² + 1
     For n ≥ 1, Q11 n = Q00(n-1) = fib(2(n-1)+1) = fib(2n-1)
     So: fib(2n+1) · fib(2n-1) = fib(2n)² + 1

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.FibCassini

open E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11 det_pn_universal)
open E213.Lib.Math.Mobius213.Px.QFibIdentity (Q00_eq_fib Q01_eq_fib Q11_eq_fib_succ)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)

/-! ## §1 — Q11 at n+1 in Fibonacci terms -/

/-- `Q11 (n+1) = fib(2n+1)` — bottom-right entry of P^(n+1) is
    the same as top-left of P^n. -/
theorem Q11_succ_eq_fib (n : Nat) : Q11 (n + 1) = fib (2 * n + 1) :=
  Q11_eq_fib_succ n

/-! ## §2 — Fibonacci Cassini at shifted index

For n ≥ 0: `fib(2n+3) · fib(2n+1) = fib(2n+2)² + 1`

This is the det identity at n+1:
  Q00(n+1) · Q11(n+1) = Q01(n+1)² + 1
  = fib(2(n+1)+1) · fib(2n+1) = fib(2(n+1))² + 1
  = fib(2n+3) · fib(2n+1) = fib(2n+2)² + 1  -/

/-- ★★★★★★★★★★ **Fibonacci Cassini (shifted form)**: for every n,
    `fib(2n+3) · fib(2n+1) = fib(2n+2) · fib(2n+2) + 1`.

    Immediate from `det_pn_universal (n+1)` + Fibonacci substitution. -/
theorem fib_cassini_shifted (n : Nat) :
    fib (2 * n + 3) * fib (2 * n + 1) =
    fib (2 * n + 2) * fib (2 * n + 2) + 1 := by
  have hdet := det_pn_universal (n + 1)
  -- hdet : Q00 (n+1) * Q11 (n+1) = Q01 (n+1) * Q01 (n+1) + 1
  rw [Q00_eq_fib (n + 1)] at hdet
  rw [Q01_eq_fib (n + 1)] at hdet
  rw [Q11_eq_fib_succ n] at hdet
  -- hdet : fib(2*(n+1)+1) * fib(2*n+1) = fib(2*(n+1)) * fib(2*(n+1)) + 1
  have h1 : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [h1, h2] at hdet
  exact hdet

/-! ## §3 — Fibonacci Cassini at base form (det at n directly)

For n ≥ 0: `fib(2n+1) · fib(2n+1) = fib(2n+2) · fib(2n) + 1`

Wait — that's not right. Let me re-derive:
  det_pn_universal n : Q00 n * Q11 n = Q01 n * Q01 n + 1
  Q00 n = fib(2n+1), Q01 n = fib(2n), Q11 n = Q00(n-1) for n≥1

For n=0: Q00 0 * Q11 0 = Q01 0 * Q01 0 + 1
         1 * 1 = 0 * 0 + 1 ✓

For n≥1: Q11 n = Q00(n-1) = fib(2(n-1)+1) = fib(2n-1)
  So: fib(2n+1) * fib(2n-1) = fib(2n) * fib(2n) + 1

We express this for n+1 to avoid subtraction:
  fib(2(n+1)+1) * fib(2n+1) = fib(2(n+1)) * fib(2(n+1)) + 1
  = fib(2n+3) * fib(2n+1) = fib(2n+2)² + 1

Which is exactly `fib_cassini_shifted`.
-/

/-- ★★★★★★★★★★ **Fibonacci Cassini (standard form)**: for every n,
    `fib(2n+1) · fib(2n−1) = fib(2n)² + 1` where we index from n=1.

    Re-stated with n+1 to keep everything in Nat:
    `fib(2*(n+1)+1) · fib(2*n+1) = fib(2*(n+1))² + 1`

    This is equivalent to `fib_cassini_shifted`. -/
theorem fib_cassini_standard (n : Nat) :
    fib (2 * (n + 1) + 1) * fib (2 * n + 1) =
    fib (2 * (n + 1)) * fib (2 * (n + 1)) + 1 :=
  fib_cassini_shifted n

/-! ## §4 — Concrete verification -/

/-- n=0: fib 3 · fib 1 = fib 2² + 1, i.e. 2 · 1 = 1 · 1 + 1 -/
theorem fib_cassini_at_0 : fib 3 * fib 1 = fib 2 * fib 2 + 1 := by decide

/-- n=1: fib 5 · fib 3 = fib 4² + 1, i.e. 5 · 2 = 3 · 3 + 1 -/
theorem fib_cassini_at_1 : fib 5 * fib 3 = fib 4 * fib 4 + 1 := by decide

/-- n=2: fib 7 · fib 5 = fib 6² + 1, i.e. 13 · 5 = 8 · 8 + 1 -/
theorem fib_cassini_at_2 : fib 7 * fib 5 = fib 6 * fib 6 + 1 := by decide

/-- n=3: fib 9 · fib 7 = fib 8² + 1, i.e. 34 · 13 = 21 · 21 + 1 -/
theorem fib_cassini_at_3 : fib 9 * fib 7 = fib 8 * fib 8 + 1 := by decide

/-- n=4: fib 11 · fib 9 = fib 10² + 1, i.e. 89 · 34 = 55 · 55 + 1 -/
theorem fib_cassini_at_4 : fib 11 * fib 9 = fib 10 * fib 10 + 1 := by decide

/-! ## §5 — Capstone: master bundle -/

/-- ★★★★★★★★★★★★ **Fibonacci Cassini master**:

    For all n : Nat, `fib(2n+3) · fib(2n+1) = fib(2n+2)² + 1`.

    Equivalently: at every **even** index m = 2k, the Cassini
    identity `fib(m+1) · fib(m−1) = fib(m)² + 1` holds (the sign
    is always +1 for even m).

    Derived from the P^n matrix determinant `det(P^n) = det(P)^n = 1`
    combined with the universal Fibonacci identity
    `Q00 n = fib(2n+1)`, `Q01 n = fib(2n)`.

    This bridges the 213-native P-orbit algebra to classical
    Fibonacci number theory. -/
theorem fib_cassini_master :
    ∀ n : Nat,
    fib (2 * n + 3) * fib (2 * n + 1) =
    fib (2 * n + 2) * fib (2 * n + 2) + 1 :=
  fib_cassini_shifted

end E213.Lib.Math.Mobius213.Px.FibCassini
