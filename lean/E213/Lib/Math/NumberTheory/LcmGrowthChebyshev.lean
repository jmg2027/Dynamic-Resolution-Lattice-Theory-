import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.NumberTheory.Lcm213
import E213.Meta.Nat.Valuation
import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberTheory.Legendre

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

open E213.Meta.Nat.NatDiv213 (add_mul_div_left_pure div_add_mod_pure div_sandwich
  div_eq_of_sandwich)
open E213.Tactic.NatHelper (mul_assoc)
open E213.Lib.Math.NumberTheory.Lcm213 (lcm213 lcm_pos dvd_lcm_left dvd_lcm_right lcm_dvd)
open E213.Meta.Nat.Valuation (dtrans vp le_vp_iff pow_vp_dvd)
open E213.Meta.Nat.PureNat (lt_two_pow)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_lcm_max)
open E213.Lib.Math.NumberTheory.Legendre (indLt_sum vp_one)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ sumTo_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)

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

/-! ## §3 — `vₚ(lcm 1..N)` as a count (the lcm-side companion to Legendre)

`vₚ(lcm 1..N) = #{f ≥ 1 : pᶠ ≤ N} = floorLog p N`, the largest `f` with `pᶠ ≤ N`.
`floorLog` is a downward search mirroring `Meta/Nat/Valuation.vpSearch`; its sandwich
`p^{floorLog} ≤ N < p^{floorLog+1}` gives the indicator bridge
`p^{e+1} ≤ N ↔ e < floorLog`, so the count is `indLt_sum`.  The valuation equals the
count by `≤` (`p^{floorLog} ∣ lcm`, `dvd_lcmUpTo`) and `≥` (each `vₚk ≤ floorLog`,
folded through `vp_lcm_max`). -/

/-! ### pow strict monotonicity (no `Nat.pow_lt_pow_right` in core) -/

private theorem lt_pow_self {p : Nat} (hp : 2 ≤ p) (k : Nat) : k < p ^ k :=
  Nat.lt_of_lt_of_le (lt_two_pow k) (Nat.pow_le_pow_left hp k)

private theorem pow_lt_succ_self {p : Nat} (hp : 2 ≤ p) (a : Nat) : p ^ a < p ^ (a + 1) := by
  have hpa : 0 < p ^ a := Nat.pos_pow_of_pos a (Nat.lt_of_lt_of_le (by decide) hp)
  rw [Nat.pow_succ]
  calc p ^ a < p ^ a + p ^ a := Nat.lt_add_of_pos_right hpa
    _ = p ^ a * 2 := by ring_nat
    _ ≤ p ^ a * p := Nat.mul_le_mul_left (p ^ a) hp

private theorem pow_lt_pow_of_lt {p a b : Nat} (hp : 2 ≤ p) (h : a < b) : p ^ a < p ^ b :=
  Nat.lt_of_lt_of_le (pow_lt_succ_self hp a)
    (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) (Nat.succ_le_of_lt h))

private theorem lt_of_pow_lt_pow {p a b : Nat} (hp : 2 ≤ p) (h : p ^ a < p ^ b) : a < b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd h (Nat.not_lt.mpr (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) hge))

/-! ### the floor-log search -/

/-- Largest `f ≤ b` with `pᶠ ≤ N` (downward search; mirror of `vpSearch`). -/
def floorLogSearch (p N : Nat) : Nat → Nat
  | 0 => 0
  | f + 1 => if p ^ (f + 1) ≤ N then f + 1 else floorLogSearch p N f

/-- `floorLog p N` = largest `f` with `pᶠ ≤ N`. -/
def floorLog (p N : Nat) : Nat := floorLogSearch p N N

private theorem floorLogSearch_pow_le {p N : Nat} (hN : 1 ≤ N) :
    ∀ b, p ^ (floorLogSearch p N b) ≤ N
  | 0 => by show p ^ 0 ≤ N; rw [Nat.pow_zero]; exact hN
  | b + 1 => by
      show p ^ (floorLogSearch p N (b + 1)) ≤ N
      unfold floorLogSearch
      by_cases h : p ^ (b + 1) ≤ N
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact floorLogSearch_pow_le hN b

private theorem floorLogSearch_le (p N : Nat) : ∀ b, floorLogSearch p N b ≤ b
  | 0 => Nat.le_refl 0
  | b + 1 => by
      unfold floorLogSearch
      by_cases h : p ^ (b + 1) ≤ N
      · rw [if_pos h]; exact Nat.le_refl _
      · rw [if_neg h]; exact Nat.le_succ_of_le (floorLogSearch_le p N b)

private theorem floorLogSearch_ge {p N : Nat} :
    ∀ b f, f ≤ b → p ^ f ≤ N → f ≤ floorLogSearch p N b
  | 0,     f, hf, _    => hf
  | b + 1, f, hf, hpow => by
      unfold floorLogSearch
      by_cases h : p ^ (b + 1) ≤ N
      · rw [if_pos h]; exact hf
      · rw [if_neg h]
        have hfb : f ≤ b := by
          rcases Nat.lt_or_eq_of_le hf with hlt | heq
          · exact Nat.le_of_lt_succ hlt
          · exact absurd (heq ▸ hpow) h
        exact floorLogSearch_ge b f hfb hpow

/-- `p^{floorLog p N} ≤ N` (`N ≥ 1`). -/
theorem floorLog_pow_le {p N : Nat} (hN : 1 ≤ N) : p ^ (floorLog p N) ≤ N :=
  floorLogSearch_pow_le hN N

/-- `floorLog p N ≤ N`. -/
theorem floorLog_le {p N : Nat} : floorLog p N ≤ N := floorLogSearch_le p N N

/-- `pᶠ ≤ N → f ≤ floorLog p N` (`p ≥ 2`). -/
theorem floorLog_ge {p N f : Nat} (hp : 2 ≤ p) (hpow : p ^ f ≤ N) : f ≤ floorLog p N :=
  floorLogSearch_ge N f (Nat.le_of_lt (Nat.lt_of_lt_of_le (lt_pow_self hp f) hpow)) hpow

/-- The upper sandwich: `N < p^{floorLog p N + 1}` (`p ≥ 2`, `N ≥ 1`). -/
theorem lt_pow_floorLog_succ {p N : Nat} (hp : 2 ≤ p) : N < p ^ (floorLog p N + 1) := by
  rcases Nat.lt_or_ge N (p ^ (floorLog p N + 1)) with h | h
  · exact h
  · exact absurd (floorLog_ge hp h) (Nat.not_le.mpr (Nat.lt_succ_self _))

/-- The indicator bridge: `p^{e+1} ≤ N ↔ e < floorLog p N` (`p ≥ 2`, `N ≥ 1`). -/
theorem pow_le_iff_lt_floorLog {p N : Nat} (hp : 2 ≤ p) (hN : 1 ≤ N) (e : Nat) :
    p ^ (e + 1) ≤ N ↔ e < floorLog p N := by
  constructor
  · intro h
    exact Nat.lt_of_succ_lt_succ
      (lt_of_pow_lt_pow hp (Nat.lt_of_le_of_lt h (lt_pow_floorLog_succ hp)))
  · intro h
    exact Nat.le_trans
      (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) h) (floorLog_pow_le hN)

/-- The count of exponents `= floorLog`. -/
theorem lcmExpCount_eq_floorLog {p N : Nat} (hp : 2 ≤ p) (hN : 1 ≤ N) :
    sumTo N (fun e => if p ^ (e + 1) ≤ N then 1 else 0) = floorLog p N := by
  have hcongr : ∀ e, e < N →
      (if p ^ (e + 1) ≤ N then 1 else 0) = (if e < floorLog p N then 1 else 0) := by
    intro e _
    by_cases h : p ^ (e + 1) ≤ N
    · rw [if_pos h, if_pos ((pow_le_iff_lt_floorLog hp hN e).mp h)]
    · rw [if_neg h, if_neg (fun he => h ((pow_le_iff_lt_floorLog hp hN e).mpr he))]
  rw [sumTo_congr N _ _ hcongr]
  exact indLt_sum N (floorLog p N) floorLog_le

/-! ### the valuation -/

/-- The lcm valuation is bounded by the floor-log, layer by layer. -/
private theorem vp_lcmUpTo_le {p : Nat} (hp : Prime213 p) :
    ∀ N, vp p (lcmUpTo N) ≤ floorLog p N
  | 0 => by rw [show lcmUpTo 0 = 1 from rfl, vp_one hp.1]; exact Nat.zero_le _
  | n + 1 => by
      have hmono : floorLog p n ≤ floorLog p (n + 1) := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · rw [hn0]; exact Nat.zero_le _
        · exact floorLog_ge hp.1 (Nat.le_trans (floorLog_pow_le hnpos) (Nat.le_succ n))
      have hvn : vp p (n + 1) ≤ floorLog p (n + 1) :=
        floorLog_ge hp.1 (le_of_dvd_pos (p ^ (vp p (n + 1))) (n + 1) (Nat.succ_pos n)
          (pow_vp_dvd p (n + 1)))
      show vp p (lcm213 (n + 1) (lcmUpTo n)) ≤ floorLog p (n + 1)
      rw [vp_lcm_max hp (Nat.succ_pos n) (lcmUpTo_pos n)]
      by_cases hc : vp p (n + 1) ≤ vp p (lcmUpTo n)
      · rw [if_pos hc]; exact Nat.le_trans (vp_lcmUpTo_le hp n) hmono
      · rw [if_neg hc]; exact hvn

/-- ★★★ **The lcm valuation as a count** (`p` prime): `vₚ(lcm 1..N) =
    Σ_{e<N} [p^{e+1} ≤ N]` — the lcm-side companion to `legendre`, ready to fold
    against the factorial floors through `count30` at `m̃ = ⌊30m/p^{e+1}⌋`. -/
theorem vp_lcmUpTo {p : Nat} (hp : Prime213 p) (N : Nat) :
    vp p (lcmUpTo N) = sumTo N (fun e => if p ^ (e + 1) ≤ N then 1 else 0) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · rw [hN0, show lcmUpTo 0 = 1 from rfl, vp_one hp.1]; rfl
  · rw [lcmExpCount_eq_floorLog hp.1 hN]
    refine Nat.le_antisymm (vp_lcmUpTo_le hp N) ?_
    exact (le_vp_iff p (lcmUpTo N) (floorLog p N) hp.1 (lcmUpTo_pos N)).mp
      (dvd_lcmUpTo (Nat.pos_pow_of_pos _ (Nat.lt_of_lt_of_le (by decide) hp.1))
        (floorLog_pow_le hN))

/-! ## §4 — step-2 prep: pure nested floor + termwise Σ-monotonicity

Reusable plumbing for the key-divisibility assembly (step 2): the nested-floor
identity `⌊⌊n/a⌋/b⌋ = ⌊n/(ab)⌋` (so `⌊15m/p^{e+1}⌋ = ⌊m̃/2⌋` for `m̃ = ⌊30m/p^{e+1}⌋`,
etc.) and `Σ`-monotonicity (to sum the per-level `count30` inequalities). -/

/-- Pure nested floor `n / (a·b) = n / a / b` (`a, b > 0`); `Nat.div_div_eq_div_mul`
    carries `propext`.  Both directions pinned by the ÷-sandwich. -/
theorem div_div_pure (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    n / (a * b) = n / a / b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have sy := div_sandwich a n ha
  have sx := div_sandwich b (n / a) hb
  refine (div_eq_of_sandwich hab ?_ ?_).symm
  · calc a * b * (n / a / b) = a * (b * (n / a / b)) := mul_assoc a b (n / a / b)
      _ ≤ a * (n / a) := Nat.mul_le_mul_left a sx.1
      _ ≤ n := sy.1
  · calc n < a * (n / a + 1) := sy.2
      _ ≤ a * (b * (n / a / b + 1)) := Nat.mul_le_mul_left a (Nat.succ_le_of_lt sx.2)
      _ = a * b * (n / a / b + 1) := (mul_assoc a b (n / a / b + 1)).symm

/-- Termwise `Σ`-monotonicity: `(∀ k<n, f k ≤ g k) → Σ_n f ≤ Σ_n g`. -/
theorem sumTo_le_sumTo : ∀ (n : Nat) (f g : Nat → Nat),
    (∀ k, k < n → f k ≤ g k) → sumTo n f ≤ sumTo n g
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, h => by
      rw [sumTo_succ, sumTo_succ]
      exact Nat.add_le_add
        (sumTo_le_sumTo n f g (fun k hk => h k (Nat.lt_succ_of_lt hk)))
        (h n (Nat.lt_succ_self n))

end E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
