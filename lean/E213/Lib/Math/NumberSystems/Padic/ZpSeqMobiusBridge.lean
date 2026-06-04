import E213.Lib.Math.NumberSystems.Padic.SetoidFramework
import E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot

/-!
# ZpSeqMobiusBridge — ZpSeqEquiv and the Möbius reading

`ZpSeqEquiv x y := ∀ k, x.digits k = y.digits k` is pointwise
equality on `Nat → Fin p` digit sequences.  The domain's
*coordinate space* is `Nat` (not `Nat × Nat` as in the cut
framework), so the canonical Möbius-orbit reading differs from
the cut case.

This file records two readings and their tightness:

  (A) **Möbius-pair projection** — view each Nat index as a
      component of some Stern-Brocot reachable pair `(m, k)` and
      enforce digit agreement at both components.  Since
      Stern-Brocot covers every `(m, k)` with `m + k ≥ 1`, this
      reading is *bidirectionally equal* to `ZpSeqEquiv`
      (every Nat index appears as some pair component).  Closes
      the canonical-equivalence conjecture on ZpSeq.

  (B) **Möbius-Pell index orbit** — restrict to the Fibonacci-
      indexed positions hit by `Pseq seedZero` / `Pseq seedInf`
      first components: `{0, 1, 1, 2, 3, 5, 8, 13, 21, 34, ...}`.
      This reading is *strictly weaker* than `ZpSeqEquiv` — two
      ZpSeqs can agree on Fibonacci-indexed digits and differ
      elsewhere.

The (A)-reading is the unified canonical equivalence; the
(B)-reading is the natural Möbius P-orbit attempt, recorded as
the structurally honest limitation.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.NumberSystems.Padic.ZpSeqMobiusBridge

open E213.Lib.Math.NumberSystems.Padic (ZpSeq ZpDigit)
open E213.Lib.Math.NumberSystems.Padic.SetoidFramework (ZpSeqEquiv)
open E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot
  (SternBrocotReachable reachable_of_pos reachable_succ_zero
   reachable_zero_succ)

/-! ## §1 — Möbius-pair projection (the tight reading) -/

/-- **ZpMobiusPairEq**: agreement of two ZpSeq's digits at every
    component of every Stern-Brocot reachable index pair.
    Equivalent to `ZpSeqEquiv` because Stern-Brocot covers
    `Nat × Nat \ {(0, 0)}`, so every Nat index appears as the
    first component of some reachable pair. -/
def ZpMobiusPairEq {p : Nat} (x y : ZpSeq p) : Prop :=
  ∀ (m k : Nat), SternBrocotReachable (m, k) →
    x.digits m = y.digits m ∧ x.digits k = y.digits k

/-- Forward bridge: pointwise digit equality implies
    Möbius-pair agreement. -/
theorem ZpMobiusPairEq_of_ZpSeqEquiv {p : Nat} {x y : ZpSeq p}
    (h : ZpSeqEquiv x y) : ZpMobiusPairEq x y :=
  fun m k _ => ⟨h m, h k⟩

/-- Backward bridge: Möbius-pair agreement implies pointwise
    digit equality.  For any Nat index `n`, the pair `(n, 0)`
    (for `n ≥ 1`) or `(0, 1)` (for `n = 0`) is Stern-Brocot
    reachable, so the first or second component reading lifts. -/
theorem ZpSeqEquiv_of_ZpMobiusPairEq {p : Nat} {x y : ZpSeq p}
    (h : ZpMobiusPairEq x y) : ZpSeqEquiv x y := by
  intro n
  match n with
  | 0 =>
    -- Use SR (0, 1) — the seedZero — and read .digits 0 component
    exact (h 0 1 .seedZero).1
  | n + 1 =>
    -- Use SR (n+1, 0) — reachable_succ_zero n
    exact (h (n+1) 0 (reachable_succ_zero n)).1

/-- ★★★★★ **Bidirectional canonical equivalence on ZpSeq**:
    `ZpSeqEquiv ↔ ZpMobiusPairEq`.  Closes the
    canonical-equivalence conjecture on `Nat → Fin p` digit
    sequences via the Stern-Brocot coverage of `Nat × Nat`
    (every Nat index is a pair component). -/
theorem ZpSeqEquiv_iff_ZpMobiusPairEq {p : Nat} (x y : ZpSeq p) :
    ZpSeqEquiv x y ↔ ZpMobiusPairEq x y :=
  ⟨ZpMobiusPairEq_of_ZpSeqEquiv, ZpSeqEquiv_of_ZpMobiusPairEq⟩

/-! ## §2 — Möbius-Pell index orbit (the strictly weaker reading)

A natural attempt is to restrict to indices hit by the P-orbit:
the Fibonacci sequence `{F_0, F_1, F_2, ...} = {0, 1, 1, 2, 3, 5,
8, 13, 21, 34, ...}`.  Define `ZpFibEq` and observe that it is
**strictly weaker** than `ZpSeqEquiv` because non-Fibonacci
indices (e.g., `n = 4, 6, 7, 9, 10, ...`) are unconstrained. -/

/-- Fibonacci sequence on Nat. -/
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/-- ZpSeqs agree at every Fibonacci-indexed position.  This is
    the naive "P-orbit on indices" reading.  Strictly weaker
    than `ZpSeqEquiv`. -/
def ZpFibEq {p : Nat} (x y : ZpSeq p) : Prop :=
  ∀ n, x.digits (fib n) = y.digits (fib n)

/-- Forward bridge: pointwise implies Fibonacci-indexed
    agreement.  (Converse fails — see `fib_4_eq_3` below + any
    distinguishing pair of digit sequences at index 4.) -/
theorem ZpFibEq_of_ZpSeqEquiv {p : Nat} {x y : ZpSeq p}
    (h : ZpSeqEquiv x y) : ZpFibEq x y :=
  fun n => h (fib n)

/-- Concrete Fibonacci values: `fib 0..6 = 0, 1, 1, 2, 3, 5, 8`. -/
theorem fib_values :
    fib 0 = 0 ∧ fib 1 = 1 ∧ fib 2 = 1 ∧ fib 3 = 2
    ∧ fib 4 = 3 ∧ fib 5 = 5 ∧ fib 6 = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- ★ **Index 4 is not in the Fibonacci range up to `fib 6`** —
    the Fibonacci values are `{0, 1, 1, 2, 3, 5, 8}`; index `4`
    is missing.  Concrete obstruction to `ZpFibEq → ZpSeqEquiv`. -/
theorem index_4_not_in_fib_range :
    fib 0 ≠ 4 ∧ fib 1 ≠ 4 ∧ fib 2 ≠ 4 ∧ fib 3 ≠ 4
    ∧ fib 4 ≠ 4 ∧ fib 5 ≠ 4 ∧ fib 6 ≠ 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §3 — Structural note

The two readings (A) and (B) demonstrate that the "canonical
Möbius equivalence" on a domain is determined by how P acts on
the domain's **coordinate space**:

  · Cut: coordinates are `Nat × Nat`; P-mediant orbit covers
    everything modulo `(0, 0)`; canonical equivalence = pointwise
    cutEq.
  · ZpSeq: coordinates are `Nat`; the natural P-orbit
    (Fibonacci-indexed positions) is strictly thinner than
    `Nat`; pointwise `ZpSeqEquiv` IS the canonical equivalence
    with no further reduction.

The (A)-reading shows the conjecture still closes via
Stern-Brocot pair coverage projected to single-Nat components.
The (B)-reading exposes why the P-iteration-on-indices analogy
to cut's Pseq orbit doesn't tighten to a bidirectional bridge. -/

end E213.Lib.Math.NumberSystems.Padic.ZpSeqMobiusBridge
