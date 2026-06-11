import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.NumberTheory.Lcm213
import E213.Meta.Nat.Valuation

/-!
# LcmGrowthChebyshev — the finitized Chebyshev 30-block bound for `lcm(1..n)`

The ζ(3) reduced presentation (`Zeta3Cut.zeta3_reduced_conditional`, input **I2**)
needs `lcm(1..n)` to grow slower than `α^{1/3} ≈ 3.236` per step, against the orbit's
`28`-geometric growth.  The clean ∅-axiom target is the **finitized Chebyshev
30-block** bound `lcm(1..n)³ ≤ 10^{43.5}·31.62ⁿ` (with `c³ = √10³ = 31.62 < 33.97 =
(1+√2)⁴`), a `7.4%`-per-`n` margin — far wider than Hanson's sub-`0.5%`, and with no
unbounded Sylvester tail.

The brick is built bottom-up; this file accumulates the chain section by section.

  * **§1 — the 30-periodic counting lemma**: `[m̃≥1] + ⌊m̃/2⌋ + ⌊m̃/3⌋ + ⌊m̃/5⌋
    ≤ m̃ + ⌊m̃/30⌋ + [m̃≥6]` for **every** `m̃` — decided on the 30 residues, then
    extended by the matching `+31`-per-`+30` increment (no induction needed: the
    `30q+r` split makes the `q`-coefficients cancel exactly).  This is the per-prime
    bucketing inequality that the key divisibility step (§2, forthcoming) folds the
    Legendre terms through, at `m̃ = ⌊30m/pʲ⌋`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.LcmGrowthChebyshev

open E213.Meta.Nat.NatDiv213 (add_mul_div_left_pure div_add_mod_pure)
open E213.Lib.Math.NumberTheory.Lcm213 (lcm213 lcm_pos dvd_lcm_left dvd_lcm_right lcm_dvd)
open E213.Meta.Nat.Valuation (dtrans)

/-! ## §1 — the 30-periodic counting lemma -/

/-- The counting inequality on a single residue block `r < 30` (decided). -/
private theorem count30_residue : ∀ r, r < 30 →
    (if 1 ≤ r then 1 else 0) + r / 2 + r / 3 + r / 5
      ≤ r + (if 6 ≤ r then 1 else 0) := by decide

/-- The indicator-free residue inequality `⌊r/2⌋+⌊r/3⌋+⌊r/5⌋ ≤ r` for `r < 30`
    (decided) — the form that survives once both indicators saturate to `1` (the
    `q ≥ 1` regime). -/
private theorem count30_residue_pos : ∀ r, r < 30 → r / 2 + r / 3 + r / 5 ≤ r := by
  decide

/-- ★★★ **The 30-periodic counting lemma**: for every `m̃`,
    `[m̃≥1] + ⌊m̃/2⌋ + ⌊m̃/3⌋ + ⌊m̃/5⌋ ≤ m̃ + ⌊m̃/30⌋ + [m̃≥6]`.

    Proof by the `m̃ = 30q + r` split (`r < 30`): the three floors split as
    `⌊(30q+r)/d⌋ = (30/d)·q + ⌊r/d⌋` and `⌊(30q+r)/30⌋ = q`, so the `q`-coefficients
    are `15+10+6 = 31` on the left and `30+1 = 31` on the right — they cancel, and
    what remains is the residue inequality (`q = 0`: `count30_residue`; `q ≥ 1`: both
    indicators are `1` and it is `count30_residue_pos`).  No exterior input; the
    period is read off the split, not assumed. -/
theorem count30 (t : Nat) :
    (if 1 ≤ t then 1 else 0) + t / 2 + t / 3 + t / 5
      ≤ t + t / 30 + (if 6 ≤ t then 1 else 0) := by
  rcases Nat.lt_or_ge t 30 with hlt | hge
  · -- `t < 30`: the residue lemma directly (`t/30 = 0`, `t + 0 ≡ t`)
    rw [Nat.div_eq_of_lt hlt]
    exact count30_residue t hlt
  · -- `t ≥ 30`: both indicators saturate to `1`; the `q`-coefficients cancel,
    -- leaving the indicator-free residue inequality
    obtain ⟨q, r, hr, ht⟩ : ∃ q r, r < 30 ∧ t = 30 * q + r :=
      ⟨t / 30, t % 30, Nat.mod_lt t (by decide), (div_add_mod_pure t 30).symm⟩
    have h1t : 1 ≤ t := Nat.le_trans (by decide) hge
    have h6t : 6 ≤ t := Nat.le_trans (by decide) hge
    rw [if_pos h1t, if_pos h6t]
    subst ht
    -- split the three floors and the period floor (`q` stays a clean variable)
    have h2 : (30 * q + r) / 2 = r / 2 + 15 * q := by
      have e : 30 * q + r = r + 2 * (15 * q) := by ring_nat
      rw [e, add_mul_div_left_pure r 2 (15 * q) (by decide)]
    have h3 : (30 * q + r) / 3 = r / 3 + 10 * q := by
      have e : 30 * q + r = r + 3 * (10 * q) := by ring_nat
      rw [e, add_mul_div_left_pure r 3 (10 * q) (by decide)]
    have h5 : (30 * q + r) / 5 = r / 5 + 6 * q := by
      have e : 30 * q + r = r + 5 * (6 * q) := by ring_nat
      rw [e, add_mul_div_left_pure r 5 (6 * q) (by decide)]
    have h30 : (30 * q + r) / 30 = q := by
      have e : 30 * q + r = r + 30 * q := by ring_nat
      rw [e, add_mul_div_left_pure r 30 q (by decide), Nat.div_eq_of_lt hr, Nat.zero_add]
    rw [h2, h3, h5, h30]
    -- canonicalize both sides to `31q + small`
    have eL : 1 + (r / 2 + 15 * q) + (r / 3 + 10 * q) + (r / 5 + 6 * q)
        = 31 * q + (1 + (r / 2 + r / 3 + r / 5)) := by ring_nat
    have eR : 30 * q + r + q + 1 = 31 * q + (1 + r) := by ring_nat
    rw [eL, eR]
    exact Nat.add_le_add_left
      (Nat.add_le_add_left (count30_residue_pos r hr) 1) (31 * q)

/-! ## §2 — the iterated lcm `lcm(1..N)` -/

/-- `lcmUpTo N = lcm(1, 2, …, N)` (empty product `lcmUpTo 0 = 1`). -/
def lcmUpTo : Nat → Nat
  | 0 => 1
  | n + 1 => lcm213 (n + 1) (lcmUpTo n)

/-- `lcm(1..N) > 0`. -/
theorem lcmUpTo_pos : ∀ N, 0 < lcmUpTo N
  | 0 => Nat.zero_lt_one
  | n + 1 => lcm_pos (n + 1) (lcmUpTo n) (Nat.succ_pos n) (lcmUpTo_pos n)

/-- Every `k ∈ [1, N]` divides `lcm(1..N)`. -/
theorem dvd_lcmUpTo : ∀ {k N : Nat}, 0 < k → k ≤ N → k ∣ lcmUpTo N
  | _, 0,     hk, hkN => absurd hk (Nat.not_lt.mpr hkN)
  | k, n + 1, hk, hkN => by
      rcases Nat.lt_or_eq_of_le hkN with hlt | heq
      · exact dtrans (dvd_lcmUpTo hk (Nat.le_of_lt_succ hlt))
          (dvd_lcm_right (n + 1) (lcmUpTo n) (lcmUpTo_pos n))
      · rw [heq]
        exact dvd_lcm_left (n + 1) (lcmUpTo n) (Nat.succ_pos n)

/-- ★★ **Universal property of `lcm(1..N)`**: any common multiple of `1, …, N` is a
    multiple of `lcm(1..N)` — the divisibility certificate step 6 closes through. -/
theorem lcmUpTo_dvd : ∀ {N m : Nat}, (∀ k, 0 < k → k ≤ N → k ∣ m) → lcmUpTo N ∣ m
  | 0,     m, _ => Nat.one_dvd m
  | n + 1, m, h => by
      refine lcm_dvd (n + 1) (lcmUpTo n) m (Nat.succ_pos n) (lcmUpTo_pos n)
        (h (n + 1) (Nat.succ_pos n) (Nat.le_refl _))
        (lcmUpTo_dvd (fun k hk hkn => h k hk (Nat.le_succ_of_le hkn)))

end E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
