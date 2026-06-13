import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Tactic.NatHelper

/-!
# BestApproximation — the cross-determinant is the Diophantine approximation deficiency

The residue's shape (`DegreeCriterion`) is the cross-determinant `W` against the
denominator growth.  This file ties that shape to the **classical Diophantine quality**
of the convergents — without the overclaim "modulus degree = irrationality measure"
(`μ` is a `limsup`, itself a reached-by-none boundary cut; see
`theory/essays/analysis/the_degree_of_a_number.md`).  The rigorous, ∅-axiom core:

  * ★★★ `denominator_lower_bound` — any rational `p/k` lying *strictly between* two
    consecutive convergents `a_i/d_i < p/k < a_{i+1}/d_{i+1}` has denominator bounded
    below by `k·W_i ≥ d_i + d_{i+1}`.  So to interpose a fraction you pay denominator
    `≥ (d_i + d_{i+1}) / W_i`: the cross-determinant `W_i` is **exactly the
    best-approximation deficiency** of the presentation at layer `i`.
  * ★★★ `unimodular_best_approximation` — at the unimodular floor `W_i = 1` (the
    Farey / continued-fraction case) this is `k ≥ d_i + d_{i+1}`: the convergents are
    *optimal* best approximations — no smaller denominator interposes.  This is the
    constructive core of the universal `μ ≥ 2` (Dirichlet) floor.

So the discrete invariant `W` (the residue's shape) measures how far the pointing is
from optimal approximation — the `μ`-content, read off the recurrence with no limit and
no `limsup`.  Pure ℕ cross-multiplication (no division, no reals).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.BestApproximation

open E213.Tactic.NatHelper (le_of_add_le_add_left)

/-- ★★★ **Best-approximation lower bound via the cross-determinant.**  If `p/k` lies
    strictly between consecutive convergents — `a_i/d_i < p/k < a_{i+1}/d_{i+1}`, in
    cross-multiplied ℕ form `a_i·k < p·d_i` and `p·d_{i+1} < a_{i+1}·k` — and the
    cross-determinant is `W` (`a_{i+1}·d_i = a_i·d_{i+1} + W`), then

        d_i + d_{i+1} ≤ k · W.

    Equivalently `k ≥ (d_i + d_{i+1}) / W`: interposing a fraction costs denominator
    inversely proportional to `W`.  The two strict gaps each contribute a `+1`
    (integer strictness), and the identity
    `(p d_i − a_i k)·d_{i+1} + (a_{i+1} k − p d_{i+1})·d_i = k·W` (here additive, no
    subtraction) carries them onto `k·W`. -/
theorem denominator_lower_bound {ai di ai1 di1 p k W : Nat}
    (hW : ai1 * di = ai * di1 + W)
    (h1 : ai * k < p * di) (h2 : p * di1 < ai1 * k) :
    di + di1 ≤ k * W := by
  have h1' : ai * k + 1 ≤ p * di := h1
  have h2' : p * di1 + 1 ≤ ai1 * k := h2
  have hA : ai * k * di1 + di1 ≤ p * di * di1 := by
    have h := Nat.mul_le_mul_right di1 h1'
    rwa [Nat.succ_mul] at h
  have hB : p * di1 * di + di ≤ ai1 * k * di := by
    have h := Nat.mul_le_mul_right di h2'
    rwa [Nat.succ_mul] at h
  have hsum := Nat.add_le_add hA hB
  have hsub : ai1 * k * di = ai * di1 * k + W * k := by
    have e : ai1 * k * di = ai1 * di * k := by ring_nat
    rw [e, hW]; ring_nat
  rw [hsub] at hsum
  have eL : ai * k * di1 + di1 + (p * di1 * di + di)
      = (ai * di1 * k + p * di * di1) + (di + di1) := by ring_nat
  have eR : p * di * di1 + (ai * di1 * k + W * k)
      = (ai * di1 * k + p * di * di1) + k * W := by ring_nat
  rw [eL, eR] at hsum
  exact le_of_add_le_add_left hsum

/-- ★★★ **The unimodular convergents are optimal best approximations.**  At the
    Farey / continued-fraction floor `W = 1`, no rational with denominator `< d_i +
    d_{i+1}` lies strictly between consecutive convergents — the constructive core of
    `μ ≥ 2`. -/
theorem unimodular_best_approximation {ai di ai1 di1 p k : Nat}
    (hW : ai1 * di = ai * di1 + 1)
    (h1 : ai * k < p * di) (h2 : p * di1 < ai1 * k) :
    di + di1 ≤ k := by
  have h := denominator_lower_bound hW h1 h2
  rwa [Nat.mul_one] at h

end E213.Lib.Math.NumberSystems.Real213.BestApproximation
