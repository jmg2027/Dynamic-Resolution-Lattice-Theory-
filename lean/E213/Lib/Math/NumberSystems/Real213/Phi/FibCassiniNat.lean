import E213.Lib.Math.Algebra.Mobius213.Px.QFibIdentity
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut
import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213PellInvariant
import E213.Meta.Nat.PureNat
import E213.Meta.Nat.NatRing213
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.NatDiv213

/-!
# FibCassiniNat — the Fibonacci convergents lie below φ (all-Nat, ∀ n)

The φ-convergent-below-φ fact in its native Nat form, avoiding the
propext-laden Int→Nat casts.  With `a := fib(2n+2)`, `b := fib(2n+1)` (the
consecutive Fibonacci pair that the Pell convergents `pellNum/pellDen` equal),
the Cassini-variant norm `a² + 1 = a·b + b²` holds for all n, and
`PhiAsCut.phiCut_false_of_norm` then reads each convergent as below φ.

The norm's inductive step — that the Möbius P-step `(a,b) ↦ (2a+b, a+b)`
preserves `a² + 1 = a·b + b²` — is **not** re-proved here: it is the shared
`Mobius213PellInvariant.pellNormStep` (the `Pseq seedZero` orbit runs the same
recurrence).  This file supplies only the `fib`-side couplings (`aR`/`bR`) and
inducts.

All ∅-axiom: Lean-core `Nat.{add_mul, mul_assoc}` pull `propext`, so this uses
the repo's PURE replacements `Meta/Nat/PureNat.{add_mul, mul_assoc, even_sq}` and
`Lib/Math/NatRing.{two_mul_eq, three_mul_eq}`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat
open E213.Lib.Math.NumberSystems.Real213.Mobius

open E213.Lib.Math.Algebra.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Meta.Nat.PureNat (add_mul mul_assoc even_sq)
open E213.Meta.Nat.NatRing213 (two_mul_eq three_mul_eq nat_add_left_cancel nat_sub_add_cancel nat_mul_assoc nat_add_mul mul_sq sq_le_imp sq_lt_imp)
open E213.Meta.Nat.NatRing213 renaming nat_mul_lt_mul_right → mul_lt_mul_r, nat_mul_lt_mul_left → mul_lt_mul_l
open E213.Tactic.NatHelper (lt_of_lt_le lt_of_le_lt)
open E213.Meta.Nat.NatDiv213 (two_cancel two_cancel_lt)

/-! ## Fibonacci couplings (all PURE, from `fib_succ_succ` = rfl) -/

/-- `a := fib(2n+2)` satisfies `a_{n+1} = 2·a_n + b_n`. -/
private theorem aR (n : Nat) :
    fib (2 * n + 4) = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by
  have e1 : fib (2 * n + 4) = fib (2 * n + 3) + fib (2 * n + 2) := rfl
  have e2 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [e1, e2]
  calc fib (2 * n + 2) + fib (2 * n + 1) + fib (2 * n + 2)
      = fib (2 * n + 2) + fib (2 * n + 2) + fib (2 * n + 1) := by
        rw [Nat.add_assoc, Nat.add_comm (fib (2 * n + 1)) (fib (2 * n + 2)),
            ← Nat.add_assoc]
    _ = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by rw [← Nat.two_mul]

/-- `b := fib(2n+1)` satisfies `b_{n+1} = a_n + b_n`. -/
private theorem bR (n : Nat) :
    fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl

/-! ## The Cassini norm ∀ n, and below-φ -/

/-- ★★ **Fibonacci Cassini norm, ∀ n**: `fib(2n+2)² + 1 = fib(2n+2)·fib(2n+1) +
    fib(2n+1)²`.  Induction with `normstep` over the fib couplings `aR`/`bR`.
    All ∅-axiom Nat. -/
theorem fib_cassini_norm (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 2) + 1
    = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have ha : fib (2 * (k + 1) + 2) = 2 * fib (2 * k + 2) + fib (2 * k + 1) := by
      rw [show 2 * (k + 1) + 2 = 2 * k + 4 from by rw [Nat.mul_succ]]; exact aR k
    have hb : fib (2 * (k + 1) + 1) = fib (2 * k + 2) + fib (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by rw [Nat.mul_succ]]; exact bR k
    rw [ha, hb]
    exact Mobius213PellInvariant.pellNormStep (fib (2 * k + 2)) (fib (2 * k + 1)) ih

/-! ## Below φ — the convergents read `false` under `phiCut` -/

/-- Convert the Cassini norm `a²+1 = a·b+b²` (with `b ≤ 2a`, so `p := 2a−b`
    satisfies `p+b = 2a`) into the `phiCut` norm form `p² + 4 = 5·b²`.  All
    additive (eliminating `a` via `2a = p+b`); PURE. -/
private theorem phiform (m k p : Nat) (hpk : p + k = 2 * m)
    (h : m * m + 1 = m * k + k * k) : p * p + 4 = 5 * (k * k) := by
  have e4mm : (2 * m) * (2 * m) = p * p + 2 * (p * k) + k * k := by
    rw [← hpk, add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm k p, ← Nat.add_assoc,
        Nat.add_assoc (p * p) (p * k) (p * k), ← Nat.two_mul (p * k)]
  have h22 : (2 * m) * (2 * m) = 4 * (m * m) := by rw [even_sq, ← mul_assoc]
  have e4mk : (2 * m) * k = p * k + k * k := by rw [← hpk, add_mul]
  have h4mk : 4 * (m * k) = 2 * ((2 * m) * k) := by
    rw [show (2 * m) * k = 2 * (m * k) from mul_assoc 2 m k, ← mul_assoc 2 2 (m * k)]
  have h4 : p * p + 2 * (p * k) + k * k + 4 = 2 * (p * k + k * k) + 4 * (k * k) := by
    rw [← e4mm, ← e4mk, h22,
        show (4 : Nat) * (m * m) + 4 = 4 * (m * m + 1) from by rw [Nat.mul_add, Nat.mul_one],
        h, Nat.mul_add, ← h4mk]
  rw [Nat.mul_add 2 (p * k) (k * k)] at h4
  have hL : p * p + 2 * (p * k) + k * k + 4 = 2 * (p * k) + (p * p + (k * k + 4)) := by
    rw [Nat.add_assoc (p * p) (2 * (p * k)) (k * k), Nat.add_assoc (p * p) (2 * (p * k) + k * k) 4,
        Nat.add_assoc (2 * (p * k)) (k * k) 4, Nat.add_comm (p * p) (2 * (p * k) + (k * k + 4)),
        Nat.add_assoc (2 * (p * k)) (k * k + 4) (p * p), Nat.add_comm (k * k + 4) (p * p),
        ← Nat.add_assoc (2 * (p * k)) (p * p) (k * k + 4)]
  have hR : 2 * (p * k) + 2 * (k * k) + 4 * (k * k) = 2 * (p * k) + (2 * (k * k) + 4 * (k * k)) :=
    Nat.add_assoc (2 * (p * k)) (2 * (k * k)) (4 * (k * k))
  rw [hL, hR] at h4
  have h5 : p * p + (k * k + 4) = 2 * (k * k) + 4 * (k * k) := nat_add_left_cancel h4
  rw [show 2 * (k * k) + 4 * (k * k) = (k * k) + 5 * (k * k) from by
        rw [show (2 : Nat) * (k * k) + 4 * (k * k) = 6 * (k * k) from by rw [← add_mul],
            show (k * k) + 5 * (k * k) = 6 * (k * k) from by
              rw [show (6 : Nat) = 1 + 5 from rfl, add_mul, Nat.one_mul]],
      show p * p + (k * k + 4) = (k * k) + (p * p + 4) from by
        rw [← Nat.add_assoc, Nat.add_comm (p * p) (k * k), Nat.add_assoc]] at h5
  exact nat_add_left_cancel h5

/-- `fib(2n+1) ≤ 2·fib(2n+2)` — Nat-subtraction faithfulness for the convergent
    (the denominator never exceeds twice the numerator). -/
private theorem den_le (n : Nat) : fib (2 * n + 1) ≤ 2 * fib (2 * n + 2) := by
  have hle : fib (2 * n + 1) ≤ fib (2 * n + 2) := by
    show fib (2 * n + 1) ≤ fib (2 * n + 1) + fib (2 * n)
    exact Nat.le_add_right _ _
  have h2 : fib (2 * n + 2) ≤ 2 * fib (2 * n + 2) := by
    have e : 2 * fib (2 * n + 2) = fib (2 * n + 2) + fib (2 * n + 2) := Nat.two_mul _
    rw [e]; exact Nat.le_add_right _ _
  exact Nat.le_trans hle h2

/-- ★★★ **Fibonacci convergents lie below φ, ∀ n** — `phiCut (fib(2n+2))
    (fib(2n+1)) = false` for every n.  The native-Nat form of "every Pell
    convergent is below φ" (`PhiCutConvergents.convergents_below_phi` had it only
    at layers 0..8 by `decide`).  Route: `fib_cassini_norm` (the Cassini norm
    ∀n) → `phiform` (norm → `(2a−b)²+4 = 5·b²`, with `den_le` giving the faithful
    Nat subtraction `p+b = 2a`) → `PhiAsCut.phiCut_false_of_norm`.  All ∅-axiom. -/
theorem fib_convergent_below_phi (n : Nat) :
    E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut (fib (2 * n + 2)) (fib (2 * n + 1)) = false := by
  have hpk : (2 * fib (2 * n + 2) - fib (2 * n + 1)) + fib (2 * n + 1)
           = 2 * fib (2 * n + 2) :=
    E213.Meta.Nat.NatRing213.nat_sub_add_cancel (den_le n)
  have hform : (2 * fib (2 * n + 2) - fib (2 * n + 1)) * (2 * fib (2 * n + 2) - fib (2 * n + 1)) + 4
             = 5 * (fib (2 * n + 1) * fib (2 * n + 1)) :=
    phiform (fib (2 * n + 2)) (fib (2 * n + 1)) (2 * fib (2 * n + 2) - fib (2 * n + 1))
      hpk (fib_cassini_norm n)
  -- `phiCut_false_of_norm` wants `5 * k * k` (= `(5*k)*k`); `hform` has `5 * (k*k)`.
  rw [← mul_assoc 5 (fib (2 * n + 1)) (fib (2 * n + 1))] at hform
  exact E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut_false_of_norm
    (fib (2 * n + 2)) (fib (2 * n + 1)) hform

/-! ## The dynamic orbit approaches φ but never satisfies the frozen relation

`05_no_exterior.md` §5.7 reads φ two ways — *frozen* (the algebraic fixed point of
`P(x) = (2x+1)/(x+1)`, i.e. the root of `x² = x + 1`, realised here as the decidable cut
`phiCut`) and *dynamic* (the limit the Pell/Fibonacci convergents `fib(2n+2)/fib(2n+1)`
approach).  This file records the ∅-axiom facts available over `Nat` about how the dynamic
orbit relates to the frozen relation — it does **not** prove an equality/identification of
two objects (that would need the real limit), only the homogeneous-`Nat` shadow:

  * the frozen relation, homogenised for a pair `(a,b)`, is `a² = a·b + b²` (`Q(a,b) = 0`);
  * every dynamic convergent satisfies the Cassini form `a² + 1 = a·b + b²` instead
    (`fib_cassini_norm`), so it sits one `Nat` step off the frozen relation;
  * hence the convergent **never** satisfies `a² = a·b + b²` (`convergent_never_frozen`),
    while lying below the frozen cut φ (`fib_convergent_below_phi`).

So the dynamic orbit approaches φ from below and never lands on the homogeneous frozen
relation — the separating step is the Cassini surplus `+1`.  (Whether this `+1` is "the
same" unit as the descent step or the overflow surplus is narrative, not proved here — no
`Nat` term links them; cf. `ReentryUnit.peel_overflow_is_unit`, which is the one place two
such units are linked.) -/

/-- ★★ **The dynamic orbit never satisfies the homogeneous frozen relation.**  No convergent
    satisfies `a² = a·b + b²` (the pair form of `x² = x + 1`): the Cassini norm gives
    `a² + 1 = a·b + b²`, so `a² = a·b + b²` would force `a² + 1 = a²`.  The convergent sits
    one `Nat` step off the frozen relation. -/
theorem convergent_never_frozen (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 2)
      ≠ fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1) := by
  intro h
  have hc := fib_cassini_norm n
  rw [← h] at hc
  exact Nat.succ_ne_self _ hc

/-- ★★ **Approaches but never reaches** (the ∅-axiom `Nat` shadow of §5.7).  Three facts of
    the dynamic-vs-frozen relation: each convergent lies below the frozen cut φ
    (`fib_convergent_below_phi`), satisfies the Cassini form `a² + 1 = a·b + b²`
    (`fib_cassini_norm`), and so never satisfies the homogeneous frozen relation
    `a² = a·b + b²` (`convergent_never_frozen`).  The orbit approaches φ and stays exactly
    the Cassini step `+1` off the frozen relation — it never lands on it.  This is a bundle
    of three `Nat` facts, not an identification of frozen with dynamic (the latter needs the
    real limit, outside the ∅-axiom `Nat` reach). -/
theorem dynamic_approaches_never_reaches_frozen (n : Nat) :
    E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut (fib (2 * n + 2)) (fib (2 * n + 1)) = false
    ∧ fib (2 * n + 2) * fib (2 * n + 2) + 1
        = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1)
    ∧ fib (2 * n + 2) * fib (2 * n + 2)
        ≠ fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1) :=
  ⟨fib_convergent_below_phi n, fib_cassini_norm n, convergent_never_frozen n⟩

/-! ## Toward the Cauchy-complete limit — consecutive-convergent cross-product

For the `CauchyCutSeq` limit construction (`Analysis/CauchyComplete`), the key
fact is that consecutive convergents differ by exactly `1` in cross-product
(equivalently `1/(den_n·den_{n+1})` in value), so they nest and the brackets
shrink.  Combined with `fib_convergent_below_phi` (all convergents below φ) and
monotone increase, this gives a constructible modulus for each rational target. -/

/-- Generic cross-product step: from the Cassini norm `A²+1 = A·B+B²`,
    `(2A+B)·B = A·(A+B) + 1` — i.e. the two consecutive convergents
    `A/B` and `(2A+B)/(A+B)` have cross-product difference exactly `1`. -/
theorem cross_gen (A B : Nat) (norm : A * A + 1 = A * B + B * B) :
    (2 * A + B) * B = A * (A + B) + 1 := by
  rw [add_mul, Nat.mul_add, show 2 * A * B = A * B + A * B from by rw [Nat.two_mul, add_mul]]
  rw [Nat.add_assoc (A * B) (A * B) (B * B), ← norm]
  rw [Nat.add_comm (A * B) (A * A + 1), Nat.add_assoc, Nat.add_comm 1 (A * B),
      ← Nat.add_assoc]

/-- **Consecutive-convergent cross-product = +1, ∀ n**:
    `fib(2n+4)·fib(2n+1) = fib(2n+2)·fib(2n+3) + 1`.  The Fibonacci form of
    "adjacent convergents differ by one unit" — the nesting/shrinking witness for
    the Cauchy limit.  From `fib_cassini_norm` via `cross_gen`. -/
theorem convergent_cross (n : Nat) :
    fib (2 * n + 4) * fib (2 * n + 1) = fib (2 * n + 2) * fib (2 * n + 3) + 1 := by
  have hA : fib (2 * n + 4) = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by
    have e1 : fib (2 * n + 4) = fib (2 * n + 3) + fib (2 * n + 2) := rfl
    have e2 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
    rw [e1, e2]
    calc fib (2 * n + 2) + fib (2 * n + 1) + fib (2 * n + 2)
        = fib (2 * n + 2) + fib (2 * n + 2) + fib (2 * n + 1) := by
          rw [Nat.add_assoc, Nat.add_comm (fib (2 * n + 1)) (fib (2 * n + 2)),
              ← Nat.add_assoc]
      _ = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by rw [← Nat.two_mul]
  have hB : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [hA, hB]
  exact cross_gen (fib (2 * n + 2)) (fib (2 * n + 1)) (fib_cassini_norm n)

/-! ## Monotonicity, positivity, and the Cauchy (antitone) property

Toward `phiCut` as a `CauchyCutSeq` limit (`Analysis/CauchyComplete`): the cut
sequence `i ↦ pellConvergentCut i` is **antitone at every rational target**
(`cs_antitone`) — its Bool value flips `true → false` at most once as `i` grows,
because the convergents strictly increase (`conv_mono`).  An antitone Bool
sequence is automatically Cauchy, so the modulus exists; `fib_odd_pos` /
`fib_lb` (the Archimedean lower bound `n+1 ≤ fib(2n+1)`) give the positivity and
unboundedness the explicit modulus needs. -/

/-- Convergents strictly increase: `conv_n < conv_{n+1}` as cross-products.
    From `convergent_cross` (the difference is exactly `1`). -/
theorem conv_mono (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 3) < fib (2 * n + 4) * fib (2 * n + 1) := by
  rw [convergent_cross n]; exact Nat.lt_succ_self _

/-- `1 ≤ fib(2i+1)` — the denominators are positive (Nat-faithful cross-mult). -/
theorem fib_odd_pos (i : Nat) : 1 ≤ fib (2 * i + 1) := by
  induction i with
  | zero => decide
  | succ k ih =>
    show 1 ≤ fib (2 * k + 3)
    have h : fib (2 * k + 3) = fib (2 * k + 2) + fib (2 * k + 1) := rfl
    rw [h]; exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- **Archimedean lower bound**: `n + 1 ≤ fib(2n+1)`.  The denominators grow at
    least linearly, so they exceed any bound — the convergents reach any rational
    target below φ in finitely many steps (constructible Cauchy modulus). -/
theorem fib_lb (n : Nat) : n + 1 ≤ fib (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have e : fib (2 * (k + 1) + 1) = fib (2 * k + 1) + fib (2 * k + 2) := by
      show fib (2 * k + 3) = fib (2 * k + 1) + fib (2 * k + 2)
      have h : fib (2 * k + 3) = fib (2 * k + 2) + fib (2 * k + 1) := rfl
      rw [h, Nat.add_comm]
    rw [e]
    have h1 : 1 ≤ fib (2 * k + 2) :=
      Nat.le_trans (fib_odd_pos k) (Nat.le_add_right _ _)
    calc k + 1 + 1 ≤ fib (2 * k + 1) + 1 := Nat.add_le_add_right ih 1
      _ ≤ fib (2 * k + 1) + fib (2 * k + 2) := Nat.add_le_add_left h1 _

/-- ★★ **Cauchy (antitone) property**: at every rational target `(m, k)`, the
    convergent cut value is antitone in the layer — `pellConvergentCut (i+1)`
    true implies `pellConvergentCut i` true (so the Bool flips at most once,
    `true → false`).  Stated on `fib`: `fib(2i+4)·k ≤ fib(2i+3)·m` (the layer
    `i+1` cut) implies `fib(2i+2)·k ≤ fib(2i+1)·m` (the layer `i` cut).  By
    `conv_mono` + positive cross-multiplication cancellation (`fib_odd_pos`). -/
theorem cs_antitone (i m k : Nat)
    (H : fib (2 * i + 4) * k ≤ fib (2 * i + 3) * m) :
    fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m := by
  have hmono : fib (2 * i + 2) * fib (2 * i + 3) ≤ fib (2 * i + 4) * fib (2 * i + 1) :=
    Nat.le_of_lt (conv_mono i)
  have hpos : 0 < fib (2 * i + 3) := fib_odd_pos (i + 1)
  have key : fib (2 * i + 3) * (fib (2 * i + 2) * k)
           ≤ fib (2 * i + 3) * (fib (2 * i + 1) * m) := by
    calc fib (2 * i + 3) * (fib (2 * i + 2) * k)
        = (fib (2 * i + 2) * fib (2 * i + 3)) * k := by
          rw [← nat_mul_assoc, Nat.mul_comm (fib (2 * i + 3)) (fib (2 * i + 2))]
      _ ≤ (fib (2 * i + 4) * fib (2 * i + 1)) * k := Nat.mul_le_mul_right k hmono
      _ = fib (2 * i + 1) * (fib (2 * i + 4) * k) := by
          rw [Nat.mul_comm (fib (2 * i + 4)) (fib (2 * i + 1)), nat_mul_assoc]
      _ ≤ fib (2 * i + 1) * (fib (2 * i + 3) * m) := Nat.mul_le_mul_left _ H
      _ = fib (2 * i + 3) * (fib (2 * i + 1) * m) := by
          rw [← nat_mul_assoc, Nat.mul_comm (fib (2 * i + 1)) (fib (2 * i + 3)), nat_mul_assoc]
  exact Nat.le_of_mul_le_mul_left key hpos

/-- Once the convergent cut fails at layer `i` (numerator exceeds), it fails at
    `i+1` — the `true → false` flip is one-directional (`cs_antitone` contrapositive). -/
theorem cs_false_stays (i m k : Nat)
    (h : ¬ (fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m)) :
    ¬ (fib (2 * i + 4) * k ≤ fib (2 * i + 3) * m) :=
  fun H => h (cs_antitone i m k H)

/-- **False propagates forward**: if the convergent cut is `false` at layer `i`,
    it is `false` at every later layer `i + d`.  This is the eventually-constant
    (Cauchy) tail on the `false` side — the convergents, once past a rational
    target below φ, stay above it.  The `true` side (a target `≥ φ`) is constant
    from layer 0 by `fib_convergent_below_phi`; together they give the Cauchy
    modulus for `phiCut := (pellConvergent).limit` (`Analysis/CauchyComplete`). -/
theorem cs_false_forward (i m k : Nat)
    (h : ¬ (fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m)) :
    ∀ d, ¬ (fib (2 * (i + d) + 2) * k ≤ fib (2 * (i + d) + 1) * m) := by
  intro d
  induction d with
  | zero => exact h
  | succ e ih =>
    have e1 : 2 * (i + (e + 1)) + 2 = 2 * (i + e) + 4 := by
      rw [show i + (e + 1) = (i + e) + 1 from rfl, Nat.mul_succ]
    have e2 : 2 * (i + (e + 1)) + 1 = 2 * (i + e) + 3 := by
      rw [show i + (e + 1) = (i + e) + 1 from rfl, Nat.mul_succ]
    rw [e1, e2]; exact cs_false_stays (i + e) m k ih

/-! ## Case A — a target `≥ φ` keeps every convergent cut `true`

If `phiCut m k = true` (target `m/k ≥ φ`) then every convergent is `≤ m/k`
(since `conv_i < φ ≤ m/k`), so the cut is `true` at every layer.  Proof routes
through φ as a mediator in squared-norm Nat form (`cut_trans`); no Int↔Nat cast. -/

/-- `fib(2i+1) ≤ fib(2i+2)` — the convergent numerator dominates its denominator
    (so every convergent ratio is `≥ 1`). -/
private theorem num_ge_den (i : Nat) : fib (2 * i + 1) ≤ fib (2 * i + 2) := by
  show fib (2 * i + 1) ≤ fib (2 * i + 1) + fib (2 * i)
  exact Nat.le_add_right _ _

/-- Core cross-multiplication: `p² < 5·b²` and `5·k² ≤ q²` give `p·k ≤ q·b`. -/
private theorem pk_le_qb (b k p q : Nat)
    (hlow : p * p < 5 * (b * b)) (hhigh : 5 * (k * k) ≤ q * q) : p * k ≤ q * b := by
  apply sq_le_imp
  rw [mul_sq, mul_sq]
  calc (p * p) * (k * k) ≤ (5 * (b * b)) * (k * k) :=
        Nat.mul_le_mul_right (k * k) (Nat.le_of_lt hlow)
    _ = (5 * (k * k)) * (b * b) := by
        rw [nat_mul_assoc, Nat.mul_comm (b * b) (k * k), ← nat_mul_assoc]
    _ ≤ (q * q) * (b * b) := Nat.mul_le_mul_right (b * b) hhigh

/-- **Cut-order transitivity through φ** (squared-norm form): with `p = 2a−b`
    (`< φ`: `p² < 5·b²`) and `q = 2m−k` (`≥ φ`: `5·k² ≤ q²`), `p+b = 2a`,
    `q+k = 2m`, conclude the lower `≤` the upper: `a·k ≤ b·m`. -/
private theorem cut_trans (a b m k p q : Nat)
    (hp : p + b = 2 * a) (hq : q + k = 2 * m)
    (hlow : p * p < 5 * (b * b)) (hhigh : 5 * (k * k) ≤ q * q) :
    a * k ≤ b * m := by
  have hpk : p * k ≤ q * b := pk_le_qb b k p q hlow hhigh
  apply two_cancel
  have l1 : 2 * (a * k) = p * k + b * k := by rw [← nat_mul_assoc, ← hp, add_mul]
  have l2 : 2 * (b * m) = q * b + k * b := by
    calc 2 * (b * m) = (2 * m) * b := by
          rw [Nat.mul_comm 2 (b * m), nat_mul_assoc b m 2, Nat.mul_comm m 2,
              Nat.mul_comm b (2 * m)]
      _ = (q + k) * b := by rw [hq]
      _ = q * b + k * b := add_mul q k b
  rw [l1, l2, Nat.mul_comm b k]
  exact Nat.add_le_add_right hpk (k * b)

/-- ★★ **Case A** (inequality form, PURE): if the target `(m, k)` satisfies the
    φ-cut inequalities `k ≤ 2m` and `5·k² ≤ (2m−k)²` (i.e. `m/k ≥ φ`), then the
    layer-`i` convergent cut is `true` (`fib(2i+2)·k ≤ fib(2i+1)·m`) for every i —
    every convergent is `≤ m/k`.  The `true`-side constant tail of the Cauchy
    sequence.  Stated with the inequalities as Prop hypotheses (extracting them
    from `phiCut m k = true` via `of_decide_eq_true` would import propext/Classical
    through the `And`-decidability; the bool→Prop extraction is the one remaining
    non-PURE step, recorded in HANDOFF). -/
theorem cs_true_of_ineqs (i m k : Nat)
    (hk2m : k ≤ 2 * m) (hhigh : 5 * (k * k) ≤ (2 * m - k) * (2 * m - k)) :
    fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m := by
  have hconv : (2 * fib (2 * i + 2) - fib (2 * i + 1)) * (2 * fib (2 * i + 2) - fib (2 * i + 1)) + 4
             = 5 * (fib (2 * i + 1) * fib (2 * i + 1)) :=
    phiform (fib (2 * i + 2)) (fib (2 * i + 1)) (2 * fib (2 * i + 2) - fib (2 * i + 1))
      (nat_sub_add_cancel (den_le i)) (fib_cassini_norm i)
  have hlow : (2 * fib (2 * i + 2) - fib (2 * i + 1)) * (2 * fib (2 * i + 2) - fib (2 * i + 1))
            < 5 * (fib (2 * i + 1) * fib (2 * i + 1)) := by
    rw [← hconv]; exact Nat.lt_add_of_pos_right (by decide)
  exact cut_trans (fib (2 * i + 2)) (fib (2 * i + 1)) m k
    (2 * fib (2 * i + 2) - fib (2 * i + 1)) (2 * m - k)
    (nat_sub_add_cancel (den_le i)) (nat_sub_add_cancel hk2m) hlow hhigh

/-! ## Case B — a target `< φ` makes the convergent cut `false` past a modulus

If `phiCut m k = false` (target `m/k < φ`) then, since the convergents climb to
φ from below, every convergent eventually exceeds `m/k`, so the cut is `false`.
The honest pure-Nat modulus: squaring the cross-inequality collapses the whole
√5 comparison to the single condition `fib(2i+1) > 2k`, reached at `i = 2k` by
the Archimedean bound `fib_lb`.  The `gt_cross`/`qb_lt_pk` pair is the strict
mirror of `cut_trans`/`pk_le_qb`. -/

/-- `x < y → 0 < y → x² < y²` (strict square monotonicity), PURE. -/
private theorem sq_strict (x y : Nat) (hy : 0 < y) (h : x < y) : x * x < y * y :=
  lt_of_le_lt (Nat.mul_le_mul_left x (Nat.le_of_lt h)) (mul_lt_mul_r hy h)

/-- **Strict cut-order through φ** (mirror of `cut_trans`): from `q·b < p·k`
    with `p+b = 2a`, `q+k = 2m`, conclude the strict `b·m < a·k`. -/
private theorem gt_cross (a b m k p q : Nat)
    (hp : p + b = 2 * a) (hq : q + k = 2 * m)
    (hqb_lt : q * b < p * k) : b * m < a * k := by
  apply two_cancel_lt
  have l1 : 2 * (a * k) = p * k + b * k := by rw [← nat_mul_assoc, ← hp, add_mul]
  have l2 : 2 * (b * m) = q * b + k * b := by
    calc 2 * (b * m) = (2 * m) * b := by
          rw [Nat.mul_comm 2 (b * m), nat_mul_assoc b m 2, Nat.mul_comm m 2,
              Nat.mul_comm b (2 * m)]
      _ = (q + k) * b := by rw [hq]
      _ = q * b + k * b := add_mul q k b
  rw [l1, l2, Nat.mul_comm k b]
  exact Nat.add_lt_add_right hqb_lt (b * k)

/-- Core strict cross-multiplication (mirror of `pk_le_qb`): with `p² + 4 = 5·b²`
    (convergent norm), `q² < 5·k²` (target below φ), and `2k < b`, derive the
    strict `q·b < p·k`.  Squaring reduces the √5 comparison to `4·k² < b²`. -/
private theorem qb_lt_pk (b k p q : Nat)
    (hpnorm : p * p + 4 = 5 * (b * b))
    (hqlt : q * q < 5 * (k * k)) (hbig : 2 * k < b) : q * b < p * k := by
  apply sq_lt_imp
  rw [mul_sq, mul_sq]
  have hbb : 0 < b := lt_of_le_lt (Nat.zero_le (2 * k)) hbig
  have h4 : 4 * (k * k) < b * b := by
    have hkk : (2 * k) * (2 * k) = 4 * (k * k) := by rw [even_sq, ← mul_assoc]
    rw [← hkk]; exact sq_strict (2 * k) b hbb hbig
  have hstep1 : (q * q) * (b * b) + (b * b) ≤ 5 * (k * k) * (b * b) := by
    calc (q * q) * (b * b) + (b * b)
        = (q * q + 1) * (b * b) := by rw [add_mul, Nat.one_mul]
      _ ≤ (5 * (k * k)) * (b * b) := Nat.mul_le_mul_right (b * b) hqlt
  have hstep2 : 5 * (k * k) * (b * b) = (p * p) * (k * k) + 4 * (k * k) := by
    calc 5 * (k * k) * (b * b)
        = (5 * (b * b)) * (k * k) := by
          rw [nat_mul_assoc 5 (k * k) (b * b), Nat.mul_comm (k * k) (b * b),
              ← nat_mul_assoc 5 (b * b) (k * k)]
      _ = (p * p + 4) * (k * k) := by rw [hpnorm]
      _ = (p * p) * (k * k) + 4 * (k * k) := add_mul (p * p) 4 (k * k)
  rw [hstep2] at hstep1
  exact Nat.lt_of_add_lt_add_right
    (lt_of_le_lt hstep1 (Nat.add_lt_add_left h4 ((p * p) * (k * k))))

/-- **Archimedean modulus**: at layer `i ≥ 2k`, the convergent denominator
    exceeds `2k` — `2k < fib(2i+1)`.  By `fib_lb` (`i+1 ≤ fib(2i+1)`); the
    explicit point where the squared cross-comparison `4k² < den²` turns on. -/
private theorem fib_gt_2k (i k : Nat) (hik : 2 * k ≤ i) : 2 * k < fib (2 * i + 1) :=
  lt_of_lt_le (Nat.lt_succ_of_le hik) (fib_lb i)

/-- Case B, sub-case `2m < k` (target below `1/2`): every convergent — being
    `≥ 1` — exceeds it, so the cut is `false` at **every** layer. -/
private theorem cs_false_of_small (i m k : Nat) (hsmall : 2 * m < k) :
    ¬ (fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m) := by
  intro hle
  have hden_pos : 0 < fib (2 * i + 1) := fib_odd_pos i
  -- den·m ≤ num·m ≤ num·k, and den·(2m) < den·k ≤ num·k, so 2·(den·m) < num·k while num·k ≤ ... contra
  have h1 : fib (2 * i + 1) * (2 * m) < fib (2 * i + 1) * k := mul_lt_mul_l hden_pos hsmall
  have h2 : fib (2 * i + 1) * k ≤ fib (2 * i + 2) * k :=
    Nat.mul_le_mul_right k (num_ge_den i)
  have h3 : fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m := hle
  have hchain : fib (2 * i + 1) * (2 * m) < fib (2 * i + 1) * m :=
    lt_of_lt_le (lt_of_lt_le h1 h2) h3
  have hge : fib (2 * i + 1) * m ≤ fib (2 * i + 1) * (2 * m) := by
    rw [show (2 : Nat) * m = m + m from Nat.two_mul m, Nat.mul_add]
    exact Nat.le_add_right _ _
  exact (Nat.not_lt.mpr hge hchain).elim

/-- Case B, sub-case `k ≤ 2m ∧ (2m−k)² < 5k²` (genuine below-φ): past the
    modulus `i ≥ 2k`, the convergent exceeds `m/k`, so the cut is `false`.
    Routes through `qb_lt_pk` (strict cross-mult, `2k < den`) + `gt_cross`. -/
private theorem cs_false_of_below (i m k : Nat) (hik : 2 * k ≤ i)
    (hk2m : k ≤ 2 * m) (hbelow : (2 * m - k) * (2 * m - k) < 5 * (k * k)) :
    ¬ (fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m) := by
  have hpnorm : (2 * fib (2 * i + 2) - fib (2 * i + 1)) * (2 * fib (2 * i + 2) - fib (2 * i + 1)) + 4
             = 5 * (fib (2 * i + 1) * fib (2 * i + 1)) :=
    phiform (fib (2 * i + 2)) (fib (2 * i + 1)) (2 * fib (2 * i + 2) - fib (2 * i + 1))
      (nat_sub_add_cancel (den_le i)) (fib_cassini_norm i)
  have hqb : (2 * m - k) * fib (2 * i + 1) < (2 * fib (2 * i + 2) - fib (2 * i + 1)) * k :=
    qb_lt_pk (fib (2 * i + 1)) k (2 * fib (2 * i + 2) - fib (2 * i + 1)) (2 * m - k)
      hpnorm hbelow (fib_gt_2k i k hik)
  have hcross : fib (2 * i + 1) * m < fib (2 * i + 2) * k :=
    gt_cross (fib (2 * i + 2)) (fib (2 * i + 1)) m k
      (2 * fib (2 * i + 2) - fib (2 * i + 1)) (2 * m - k)
      (nat_sub_add_cancel (den_le i)) (nat_sub_add_cancel hk2m) hqb
  exact fun hle => (Nat.not_lt.mpr hle hcross).elim

/-- ★★★ **Convergent cut stabilizes to `phiCut`, ∀ target, past the modulus.**
    For every `(m, k)` and every layer `i ≥ 2k`, the convergent cut value equals
    the closed-form φ-cut: `decide (fib(2i+2)·k ≤ fib(2i+1)·m) = phiCut m k`.
    This is **stronger than Cauchy** — the sequence is eventually *constant* and
    equal to `phiCut`.  Case A (`phiCut = true`, target `≥ φ`) holds at every
    layer (`cs_true_of_ineqs`); case B (`false`, target `< φ`) holds past `i = 2k`
    (`cs_false_of_small`/`cs_false_of_below` via the Archimedean modulus).  All
    ∅-axiom.  The bridge from the rational convergent sequence to φ-as-one-Cut. -/
theorem cs_eq_phiCut (i m k : Nat) (hik : 2 * k ≤ i) :
    decide (fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m)
    = E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut m k := by
  unfold E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut
  by_cases hcut : k ≤ 2 * m ∧ 5 * k * k ≤ (2 * m - k) * (2 * m - k)
  · -- target ≥ φ: cut true at every layer
    obtain ⟨hk2m, hhigh⟩ := hcut
    have hhigh' : 5 * (k * k) ≤ (2 * m - k) * (2 * m - k) := by
      rw [mul_assoc 5 k k] at hhigh; exact hhigh
    rw [decide_eq_true (cs_true_of_ineqs i m k hk2m hhigh'), decide_eq_true ⟨hk2m, hhigh⟩]
  · -- target < φ: cut false past the modulus
    rw [decide_eq_false hcut]
    apply decide_eq_false
    by_cases hk2m : k ≤ 2 * m
    · -- genuine below-φ: ¬(5k² ≤ (2m−k)²) ⟹ (2m−k)² < 5k²
      have hbelow0 : ¬ (5 * k * k ≤ (2 * m - k) * (2 * m - k)) :=
        fun h => hcut ⟨hk2m, h⟩
      have hbelow : (2 * m - k) * (2 * m - k) < 5 * (k * k) := by
        rw [← mul_assoc 5 k k]; exact Nat.lt_of_not_le hbelow0
      exact cs_false_of_below i m k hik hk2m hbelow
    · -- target < 1/2: false at every layer
      exact cs_false_of_small i m k (Nat.lt_of_not_le hk2m)

end E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat
