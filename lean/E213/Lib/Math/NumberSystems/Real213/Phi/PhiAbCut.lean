import E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat
import E213.Lib.Math.NumberSystems.Real213.AbCutSeq
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut
import E213.Lib.Math.Analysis.Cauchy.PellSeq
import E213.Meta.Nat.PureNat

/-!
# PhiAbCut — φ as an `AbCutSeq`, and the algebraic/transcendental split as a theorem

`AbCutSeq` (`Real213/AbCutSeq.lean`) abstracts "every monotone-bounded ab-sequence
is a `Real213` cut", with `EulerCut` (e) and `PiCut` (π) as instances whose
completion modulus is a **hypothesis** — no transcendental supplies a LEM-free
total modulus.

This file makes **φ** an `AbCutSeq` too — and thereby turns the
algebraic/transcendental contrast from prose into a theorem.  The even-indexed
Fibonacci convergents `fib(2n+2)/fib(2n+1)` climb monotonically to φ (the
monotonicity step is *exactly* the Cassini norm `fib_cassini_norm`, giving the
`+1` gap `fib(2n+2)·fib(2n+3) + 1 = fib(2n+4)·fib(2n+1)`), so φ fits the same
carrier as e and π.

The difference is sharp and now formal: φ's `AbCutSeq` completes
**unconditionally** — `phi_cut_eventually_const` supplies the order-Cauchy modulus
`N(m,k) = 2k` with *no* hypothesis (from `FibCassiniNat.cs_eq_phiCut`, the exact
eventual-constancy that algebraicity buys), so `phiCompletion : CauchyCutSeq` is a
closed term and `phiCompletion_limit_eq_phiCut` lands on the closed-form
`PhiAsCut.phiCut`.  e and π have no such closed-form modulus; their `toCauchy`
needs the modulus handed in.  Same structure, the algebraicity is exactly the
closed-form modulus.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Phi.PhiAbCut

open E213.Theory (Raw)
open E213.Lib.Math.Algebra.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat (fib_cassini_norm fib_odd_pos cs_eq_phiCut)
open E213.Lib.Math.NumberSystems.Real213 (AbCutSeq)
open E213.Lib.Math.Analysis.Cauchy.PellSeq (abLens_witness)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.Analysis.Cauchy.MonotonicBounded (IsAbMonotonic IsAbPositiveB)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)
open E213.Meta.Nat.PureNat (add_mul)

/-! ## §1 — the Cassini monotonicity step -/

/-- The convergent-ratio monotonicity, reduced to the Cassini norm: with
    `a = fib(2n+2)`, `b = fib(2n+1)` and `fib(2n+3) = a+b`, `fib(2n+4) = (a+b)+a`,
    `a·(a+b) + 1 = ((a+b)+a)·b` — i.e. the adjacent cross-products differ by
    exactly `1`, so the ratios strictly increase toward φ. -/
private theorem cassini_mono_step (a b : Nat) (hc : a*a + 1 = a*b + b*b) :
    a * (a + b) + 1 = ((a + b) + a) * b := by
  rw [Nat.mul_comm a (a+b), add_mul, add_mul, add_mul,
      Nat.add_right_comm (a*a) (b*a) 1, hc, Nat.mul_comm b a]

/-- `1 ≤ fib(2n+2)` (even-index positivity, from odd-index `fib_odd_pos`). -/
private theorem fib_even_pos (n : Nat) : 1 ≤ fib (2*n+2) :=
  Nat.le_trans (fib_odd_pos n) (Nat.le_add_right _ _)

/-! ## §2 — the Fibonacci `Raw` sequence and its `AbCutSeq` -/

/-- **φ's convergent `Raw` sequence**: layer `n` is the pair `(fib(2n+2),
    fib(2n+1))`, the even/odd Fibonacci convergent of φ. -/
def fibRaw (n : Nat) : {r : Raw // abLens.view r = (fib (2*n+2), fib (2*n+1))} :=
  abLens_witness (fib (2*n+2) + fib (2*n+1)) (fib (2*n+2)) (fib (2*n+1)) rfl
    (fib_even_pos n) (fib_odd_pos n)

def fibRawSeq : Nat → Raw := fun n => (fibRaw n).val

theorem fibRaw_view (n : Nat) :
    abLens.view (fibRawSeq n) = (fib (2*n+2), fib (2*n+1)) := (fibRaw n).property

/-- ★★ **Monotone**: the Fibonacci convergents climb (the `+1` Cassini gap). -/
theorem fib_isAbMonotonic : IsAbMonotonic fibRawSeq := by
  intro n
  rw [fibRaw_view, fibRaw_view]
  show fib (2*n+2) * fib (2*(n+1)+1) ≤ fib (2*(n+1)+2) * fib (2*n+1)
  have hi2 : 2*(n+1)+1 = 2*n+3 := by rw [Nat.mul_succ]
  have hi4 : 2*(n+1)+2 = 2*n+4 := by rw [Nat.mul_succ]
  rw [hi2, hi4]
  have key : fib (2*n+2) * fib (2*n+3) + 1 = fib (2*n+4) * fib (2*n+1) := by
    have e4 : fib (2*n+4) = fib (2*n+3) + fib (2*n+2) := rfl
    have e3 : fib (2*n+3) = fib (2*n+2) + fib (2*n+1) := rfl
    rw [e3, e4, e3]
    exact cassini_mono_step (fib (2*n+2)) (fib (2*n+1)) (fib_cassini_norm n)
  rw [← key]; exact Nat.le_add_right _ 1

/-- ★ **Positive denominators** (`fib_odd_pos`). -/
theorem fib_isAbPositiveB : IsAbPositiveB fibRawSeq := by
  intro n; rw [fibRaw_view]; exact fib_odd_pos n

/-- ★★★ **φ as an `AbCutSeq`** — the same carrier as e (`EulerCut.eAb`) and π
    (`PiCut.piHalfAb`).  Inherits the whole cut interface (`cut_valid`,
    `cut_false_fwd`, `toCauchy_limit_valid`, `limit_brackets`). -/
def phiAb : AbCutSeq := ⟨fibRawSeq, fib_isAbMonotonic, fib_isAbPositiveB⟩

/-- `phiAb`'s layer cut is the convergent-cut value
    `decide (fib(2n+2)·k ≤ fib(2n+1)·m)`. -/
theorem phiAb_cut_eq (n m k : Nat) :
    phiAb.cut n m k = decide (fib (2*n+2) * k ≤ fib (2*n+1) * m) := by
  show E213.Lib.Math.Analysis.Cauchy.Archimedean.orderProj m k (abLens.view (fibRawSeq n)) = _
  rw [fibRaw_view]; rfl

/-! ## §3 — the contrast: φ completes UNCONDITIONALLY -/

/-- ★★★ **φ's order-Cauchy modulus is closed-form (`N = 2k`), no hypothesis.**
    Past `2k` the convergent cut is *exactly* `phiCut m k`
    (`cs_eq_phiCut`) — the eventual constancy that algebraicity buys.  Contrast
    e/π, whose `AbCutSeq.toCauchy` takes the modulus as a hypothesis (no LEM-free
    total modulus exists). -/
theorem phi_cut_eventually_const (m k i j : Nat) (hi : i ≥ 2*k) (hj : j ≥ 2*k) :
    phiAb.cut i m k = phiAb.cut j m k := by
  rw [phiAb_cut_eq, phiAb_cut_eq, cs_eq_phiCut i m k hi, cs_eq_phiCut j m k hj]

/-- ★★★ **φ's completion is a closed term** — the `AbCutSeq` completed with the
    closed-form modulus `N(m,k) = 2k`, unconditionally (unlike e/π). -/
def phiCompletion : CauchyCutSeq :=
  phiAb.toCauchy (fun _ k => 2*k)
    (fun m k i j hi hj => phi_cut_eventually_const m k i j hi hj)

/-- ★ φ's completion limit is a real (`ValidCut`) — no hypothesis. -/
theorem phiCompletion_limit_valid : ValidCut phiCompletion.limit :=
  phiAb.toCauchy_limit_valid _ _

/-- ★★★ **φ's `AbCutSeq` completion lands on the closed-form `phiCut`.**  The
    generic completion machinery, applied to φ with its closed-form modulus,
    recovers exactly `PhiAsCut.phiCut` — algebraicity = the limit is already a
    decidable closed-form cut, reached unconditionally. -/
theorem phiCompletion_limit_eq_phiCut (m k : Nat) :
    phiCompletion.limit m k = E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut m k := by
  show phiAb.cut (2*k) m k = E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut m k
  rw [phiAb_cut_eq]
  exact cs_eq_phiCut (2*k) m k (Nat.le_refl _)

end E213.Lib.Math.NumberSystems.Real213.Phi.PhiAbCut
