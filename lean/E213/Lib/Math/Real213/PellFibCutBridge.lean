import E213.Lib.Math.Mobius213
import E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock
import E213.Lib.Math.Real213.PhiCut
import E213.Lib.Math.Real213.FibCassiniNat
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Meta.Int213
import E213.Meta.Nat.NatRing213

/-!
# PellFibCutBridge — the Pell convergents ARE the Fibonacci convergents (∀n, PURE)

`PhiCut.pellNum`/`pellDen` are `Int`-sequence read-outs
(`(P_numerator.seq n).toNat`), while `FibCassiniNat` works natively on `fib`.
Numerically they coincide (`pell_nat_values`), but the ∀n equation was blocked by
the `Int→Nat` `toNat` cast (every Lean-core cast lemma pulls `propext`).

This file clears that wall.  The key observations:

  * `((n : Nat) : Int).toNat = n` is **`rfl`** (PURE) — the `toNat` of a manifest
    `natCast` collapses definitionally, so the cast is harmless *when the Int is
    presented as a `natCast`*.
  * So it suffices to prove the `Int`-level equation
    `P_numerator.seq n = ((fib(2n+2) : Nat) : Int)` (and den/`fib(2n+1)`), which
    is a clean 2-step induction over the shared recurrence
    `a(n+2) = 3·a(n+1) − a(n)` (`= 3·a(n+1) + (−1)·a(n) + 0`), matched on the
    `fib` side by the Nat identity `fib(2n+6) + fib(2n+2) = 3·fib(2n+4)`
    (`fib_even_3step`) — all additive, no `Int` subtraction, no `omega`.

Result: `pellNum n = fib(2n+2)` and `pellDen n = fib(2n+1)` ∀n, PURE.  This lets
the canonical `PhiCut.pellConvergentCut` inherit everything proved natively on
`fib` (the φ-cut stabilization `FibCassiniNat.cs_eq_phiCut`, hence the Cauchy
limit), retiring the native-Nat twin's "no PURE bridge" caveat.
-/

namespace E213.Lib.Math.Real213.PellFibCutBridge

open E213.Lib.Math.Mobius213 (P_numerator P_denominator)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Meta.Nat.NatRing213 (three_mul_eq two_mul_eq)
open E213.Meta.Int213

/-! ## The shared Nat 3-step identity -/

/-- **Fibonacci even-index 3-step**: `fib(2n+6) + fib(2n+2) = 3·fib(2n+4)`.
    The `fib`-side of the Pell recurrence `a(n+2) = 3·a(n+1) − a(n)`, in additive
    form.  By the recurrence `fib(2n+4) = fib(2n+3) + fib(2n+2)`. -/
theorem fib_even_3step (n : Nat) : fib (2*n+6) + fib (2*n+2) = 3 * fib (2*n+4) := by
  have e6 : fib (2*n+6) = fib (2*n+4) + fib (2*n+4) + fib (2*n+3) := by
    show (fib (2*n+4) + fib (2*n+3)) + fib (2*n+4) = fib (2*n+4) + fib (2*n+4) + fib (2*n+3)
    rw [Nat.add_right_comm]
  have e4 : fib (2*n+4) = fib (2*n+3) + fib (2*n+2) := rfl
  rw [e6, Nat.add_assoc (fib (2*n+4) + fib (2*n+4)) (fib (2*n+3)) (fib (2*n+2)),
      ← e4, three_mul_eq, two_mul_eq]

/-! ## Int-level recurrence-matching algebra (PURE, no subtraction) -/

/-- From the additive Nat identity `F2 + F0 = 3·F1` (cast to `Int`), recover the
    recurrence read-out `3·F1 + (−1)·F0 + 0 = F2`.  `Int.add_right_neg` pulls
    `propext`, so this routes through the PURE `Int213.{add_comm, add_left_neg,
    add_assoc, neg_mul}`. -/
private theorem recur_match (F0 F1 F2 : Int) (h : F2 + F0 = 3 * F1) :
    3 * F1 + (-1) * F0 + 0 = F2 := by
  rw [Int.add_zero, ← h,
      show (-1 : Int) * F0 = -F0 from by rw [neg_mul, Int.one_mul],
      add_assoc,
      show F0 + -F0 = 0 from by rw [add_comm, add_left_neg],
      Int.add_zero]

/-! ## The bridge: seq n = (fib · : Int), ∀n, by 2-step induction -/

/-- Paired invariant for the numerator: `seq n = fib(2n+2)` **and**
    `seq(n+1) = fib(2n+4)` simultaneously (the 2-step induction carrier). -/
private theorem num_pair (n : Nat) :
    P_numerator.seq n = ((fib (2*n+2) : Nat) : Int)
    ∧ P_numerator.seq (n+1) = ((fib (2*(n+1)+2) : Nat) : Int) := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    -- seq(k+2) = 3·seq(k+1) + (-1)·seq(k) + 0 ;  index 2*(k+1+1)+2 = 2*(k+2)+2 = 2k+6
    have hrec : P_numerator.seq (k+1+1)
        = 3 * P_numerator.seq (k+1) + (-1) * P_numerator.seq k + 0 :=
      P_numerator.seq_recurrence k
    have hidx2 : 2*(k+1+1)+2 = 2*k+6 := by rw [Nat.mul_add, Nat.mul_add]
    have hidx1 : 2*(k+1)+2 = 2*k+4 := by rw [Nat.mul_add]
    have hcast : ((fib (2*k+6) : Nat) : Int) + ((fib (2*k+2):Nat):Int)
               = 3 * ((fib (2*k+4):Nat):Int) := by
      show (((fib (2*k+6) + fib (2*k+2)) : Nat) : Int) = (((3 * fib (2*k+4)) : Nat) : Int)
      rw [fib_even_3step]
    show P_numerator.seq (k+1+1) = ((fib (2*(k+1+1)+2) : Nat) : Int)
    rw [hrec, h0, h1, hidx1, hidx2]
    exact recur_match _ _ _ hcast

/-- Paired invariant for the denominator: `seq n = fib(2n+1)` and
    `seq(n+1) = fib(2n+3)`. -/
private theorem den_pair (n : Nat) :
    P_denominator.seq n = ((fib (2*n+1) : Nat) : Int)
    ∧ P_denominator.seq (n+1) = ((fib (2*(n+1)+1) : Nat) : Int) := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    have hrec : P_denominator.seq (k+1+1)
        = 3 * P_denominator.seq (k+1) + (-1) * P_denominator.seq k + 0 :=
      P_denominator.seq_recurrence k
    have hidx2 : 2*(k+1+1)+1 = 2*k+5 := by rw [Nat.mul_add, Nat.mul_add]
    have hidx1 : 2*(k+1)+1 = 2*k+3 := by rw [Nat.mul_add]
    have hcast : ((fib (2*k+5) : Nat) : Int) + ((fib (2*k+1):Nat):Int)
               = 3 * ((fib (2*k+3):Nat):Int) := by
      show (((fib (2*k+5) + fib (2*k+1)) : Nat) : Int) = (((3 * fib (2*k+3)) : Nat) : Int)
      rw [show fib (2*k+5) + fib (2*k+1) = 3 * fib (2*k+3) from by
            have e5 : fib (2*k+5) = fib (2*k+3) + fib (2*k+3) + fib (2*k+2) := by
              show (fib (2*k+3) + fib (2*k+2)) + fib (2*k+3)
                 = fib (2*k+3) + fib (2*k+3) + fib (2*k+2)
              rw [Nat.add_right_comm]
            have e3 : fib (2*k+3) = fib (2*k+2) + fib (2*k+1) := rfl
            rw [e5, Nat.add_assoc (fib (2*k+3) + fib (2*k+3)) (fib (2*k+2)) (fib (2*k+1)),
                ← e3, three_mul_eq, two_mul_eq]]
    show P_denominator.seq (k+1+1) = ((fib (2*(k+1+1)+1) : Nat) : Int)
    rw [hrec, h0, h1, hidx1, hidx2]
    exact recur_match _ _ _ hcast

/-! ## ★ The bridge equations, ∀n, PURE -/

/-- ★★★ **`pellNum n = fib(2n+2)`, ∀n** — the Pell numerator read-out equals the
    even-index Fibonacci.  The `toNat` collapses by `rfl` once the `Int` seq is
    pinned to a `natCast` (`num_pair`). -/
theorem pellNum_eq_fib (n : Nat) :
    E213.Lib.Math.Real213.PhiCut.pellNum n = fib (2*n+2) := by
  show (P_numerator.seq n).toNat = fib (2*n+2)
  rw [(num_pair n).1]; rfl

/-- ★★★ **`pellDen n = fib(2n+1)`, ∀n** — the Pell denominator read-out equals the
    odd-index Fibonacci. -/
theorem pellDen_eq_fib (n : Nat) :
    E213.Lib.Math.Real213.PhiCut.pellDen n = fib (2*n+1) := by
  show (P_denominator.seq n).toNat = fib (2*n+1)
  rw [(den_pair n).1]; rfl

/-! ## ★ Canonical capstone — `pellConvergentCut` stabilizes to `phiCut`

With the bridge equations, the canonical `PhiCut.pellConvergentCut` inherits the
native-`fib` φ-cut stabilization (`FibCassiniNat.cs_eq_phiCut`) directly — no
longer only the native-Nat twin. -/

/-- ★★★ **The canonical Pell convergent cut stabilizes to `phiCut`.**  For every
    target `(m, k)` and every layer `i ≥ 2k`,
    `pellConvergentCut i m k = phiCut m k` — the `Int`-seq-defined convergent cut
    (`PhiCut.pellConvergentCut`) is eventually *constant* and equal to the
    closed-form golden-ratio cut.  The bridge (`pellNum_eq_fib`/`pellDen_eq_fib`)
    transports `FibCassiniNat.cs_eq_phiCut` onto the canonical object.  PURE. -/
theorem pellConvergentCut_eq_phiCut (i m k : Nat) (hik : 2 * k ≤ i) :
    E213.Lib.Math.Real213.PhiCut.pellConvergentCut i m k
    = E213.Lib.Math.Real213.PhiAsCut.phiCut m k := by
  show decide
      (E213.Lib.Math.Real213.PhiCut.pellNum i * k
        ≤ E213.Lib.Math.Real213.PhiCut.pellDen i * m)
    = E213.Lib.Math.Real213.PhiAsCut.phiCut m k
  rw [pellNum_eq_fib, pellDen_eq_fib]
  exact E213.Lib.Math.Real213.FibCassiniNat.cs_eq_phiCut i m k hik

end E213.Lib.Math.Real213.PellFibCutBridge
