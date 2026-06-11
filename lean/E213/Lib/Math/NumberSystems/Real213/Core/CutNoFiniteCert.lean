import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Tactic.NatHelper

/-!
# CutNoFiniteCert — cut equality has no finite certificate (the continuum dual)

`cutEq cx cy := ∀ m k, cx m k = cy m k` (`CutPoset`): two cuts are equal iff
their readouts agree at *every* resolution `(m, k)`.  This file shows that
quantifier does **not** collapse to a finite check — the continuum dual of the
integer side's finite certificate.

On the integer side `FoldCriterion.pow_eq_pow_iff_vp_support` +
`vp_eq_zero_of_gt` make "equal" a **finite** certificate: the prime-exponent
readout is *cofinitely trivial* (`vp p n = 0` for `p > n`), so only finitely
many primes — those `≤ n` — need checking.

The continuum has no such collapse:

  * ★★ `cut_no_finite_certificate` — for **every** resolution bound `N`, the two
    *distinct* rationals `N/(N+1)` and `(N+1)/(N+2)` have cuts that **agree at
    every level `k ≤ N`** yet are **not** `cutEq`.  So no finite truncation
    certifies cut equality: a non-trivial cut carries information at arbitrarily
    fine resolution.

The two rationals straddle no fraction of denominator `≤ N` (their gap is
`1/((N+1)(N+2))`, and every `m/k` with `k ≤ N` lands outside the interval), so
both readouts equal `decide (k ≤ m)` for `k ≤ N` (`key`); they first separate at
the mediant `(2N+1)/(2N+3)`, of denominator `2N+3 > N`.

**Bridge 1 of `slot_tower_crossdomain.md`, the honest half.**  The equality
certificate's *size* is the discrete/continuum boundary: **finite** for
integers (cofinitely-trivial readout, an earned theorem = UFD), **unbounded**
for reals (full-support readout, here exhibited).  The shared "∀-level local
check" shape is real but thin; the genuine content is this finite-vs-unbounded
split — a *distinction pinned* on both sides (as in bridge 4), not a forced
single schema.

All ∅-axiom: `ring_nat` polynomial identities, the pure
`NatHelper.le_of_add_le_add_left`, and a local funext-free `decide` congruence.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Core.CutNoFiniteCert

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- `decide` congruence without `funext`/`propext`: equal propositions decide
    alike, by casing on the two Bool readouts.  (Local; keeps the file ∅-axiom
    where `decide_eq_decide` would route through `propext`.) -/
private theorem decideCongr {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p = decide q := by
  cases hp : decide p with
  | true  => exact (decide_eq_true (h.mp (of_decide_eq_true hp))).symm
  | false =>
    cases hq : decide q with
    | true  => exact absurd (h.mpr (of_decide_eq_true hq)) (of_decide_eq_false hp)
    | false => rfl

/-- **Threshold law.**  For `k ≤ c`, the cut test `c·k ≤ (c+1)·m` (i.e. the cut
    of `c/(c+1)` at `m/k`) holds exactly when `k ≤ m`.  Below the resolution `c`
    the rational `c/(c+1)` rounds to `1`: the readout is `decide (k ≤ m)`.

    Forward: if `m < k` then `(c+1)(m+1) ≤ (c+1)k`, i.e.
    `(c+1)m + (c+1) ≤ c·k + k ≤ (c+1)m + k`, forcing `c+1 ≤ k ≤ c` — absurd.
    Backward: `k ≤ m ⇒ c·k ≤ c·m ≤ (c+1)·m`. -/
theorem key {c m k : Nat} (hkc : k ≤ c) :
    (c * k ≤ (c + 1) * m) ↔ (k ≤ m) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge m k with hmk | hmk
    · exfalso
      have h1 : (c + 1) * (m + 1) ≤ (c + 1) * k := Nat.mul_le_mul_left _ hmk
      have e1 : (c + 1) * (m + 1) = (c + 1) * m + (c + 1) := by ring_nat
      have e2 : (c + 1) * k = c * k + k := by ring_nat
      rw [e1, e2] at h1
      have h3 : (c + 1) * m + (c + 1) ≤ (c + 1) * m + k :=
        Nat.le_trans h1 (Nat.add_le_add_right h k)
      have h4 : c + 1 ≤ k := E213.Tactic.NatHelper.le_of_add_le_add_left h3
      exact absurd (Nat.le_trans h4 hkc) (Nat.not_succ_le_self c)
    · exact hmk
  · intro h
    have hcm : c * k ≤ c * m := Nat.mul_le_mul_left _ h
    have e : (c + 1) * m = c * m + m := by ring_nat
    rw [e]
    exact Nat.le_trans hcm (Nat.le_add_right (c * m) m)

/-- ★★ **Cut equality has no finite certificate.**  For every resolution bound
    `N`, the cuts of the *distinct* rationals `N/(N+1)` and `(N+1)/(N+2)` agree
    at every level `k ≤ N` yet are not `cutEq` — they first separate at the
    mediant `(2N+1)/(2N+3)`, of denominator `2N+3 > N`.

    So unlike the integer certificate (finite support, cofinitely-trivial
    readout), the real certificate is **unbounded**: distinguishing two reals
    can require arbitrarily fine resolution.  This is the continuum side of
    bridge 1's certificate-size distinction. -/
theorem cut_no_finite_certificate (N : Nat) :
    (∀ m k, k ≤ N → constCut N (N + 1) m k = constCut (N + 1) (N + 2) m k)
    ∧ ¬ cutEq (constCut N (N + 1)) (constCut (N + 1) (N + 2)) := by
  refine ⟨?_, ?_⟩
  · intro m k hk
    show decide (N * k ≤ (N + 1) * m) = decide ((N + 1) * k ≤ (N + 2) * m)
    rw [decideCongr (key hk), decideCongr (key (Nat.le_trans hk (Nat.le_succ N)))]
  · intro hce
    have hval := hce (2 * N + 1) (2 * N + 3)
    have cxT : constCut N (N + 1) (2 * N + 1) (2 * N + 3) = true := by
      show decide (N * (2 * N + 3) ≤ (N + 1) * (2 * N + 1)) = true
      apply decide_eq_true
      have e : (N + 1) * (2 * N + 1) = N * (2 * N + 3) + 1 := by ring_nat
      rw [e]; exact Nat.le_succ _
    have cyF : constCut (N + 1) (N + 2) (2 * N + 1) (2 * N + 3) = false := by
      show decide ((N + 1) * (2 * N + 3) ≤ (N + 2) * (2 * N + 1)) = false
      apply decide_eq_false
      have e : (N + 1) * (2 * N + 3) = (N + 2) * (2 * N + 1) + 1 := by ring_nat
      rw [e]; exact Nat.not_succ_le_self _
    rw [cxT, cyF] at hval
    exact Bool.noConfusion hval

end E213.Lib.Math.NumberSystems.Real213.Core.CutNoFiniteCert
