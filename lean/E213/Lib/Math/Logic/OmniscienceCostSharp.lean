import E213.Lib.Math.Logic.RealDichotomyLLPO
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# Sharp omniscience cost — the minimal certifying denominator of the LLPO sign-decision

`RealDichotomyLLPO` calibrates the exact real sign-dichotomy to `LLPO` by encoding an
at-most-one-true `f` as a cut `y_f ∈ {1, 1±2^{-(n+1)}}` (fire at index `n`).  Its
`odd_probe_yf_true` certifies the odd case at a *non-minimal* resolution
`k = n+1+2^{n+1}`, and the docstring remarks informally that the gap `1 − y_f =
2^{-(n+1)}` forces denominator `~2^{n+1}` — "the omniscience cost."

This file makes that **sharp and two-sided**.  Call `k` a *certifying denominator*
for an odd fire if some rational `m/k` separates `y_f` strictly below `1`
(`one m k = false`, i.e. `m/k < 1`, and `yf f m k = true`, i.e. `y_f ≤ m/k`):

  `OddCertifies f k := ∃ m, one m k = false ∧ yf f m k = true`.

> ★★★ **The minimal certifying denominator is exactly `2^{n+1}`.**
>   * `odd_cert_at_pow` (UB): `k = 2^{n+1}`, `m = 2^{n+1}−1` certifies — the boundary
>     rational `m/k = y_f` exactly (the cut's `≤` lets the endpoint certify).
>   * `odd_no_cert_below` (LB): **no** `k < 2^{n+1}` certifies, for any `m`.
>   * `odd_min_cert_denom`: `2^{n+1}` is the least certifying denominator.

The content is the elementary fact "any rational in `[1−2^{-(n+1)}, 1)` has denominator
`≥ 2^{n+1}`", but pinned as the **sharp, instance-indexed price of the LLPO-gated order
decision** — respecting non-uniformity: the bound depends on the per-instance fire index
`n`, and `2^{n+1} → ∞`, so no `f`-independent (uniform) certifying denominator exists.

**The cost is one-sided.** The dual even case (`y_f = 1+2^{-(n+1)} > 1`) is *cheap*: the
threshold rational `1 = k/k` already lies in `[1, y_f)`, so a certificate refuting
`y_f ≤ 1` exists at denominator `n+1` (`even_cert_cheap`), far below `2^{n+1}`
(`cost_asymmetric`).  The exponential price attaches only to separating a value
*approaching `1` from below* by a *sub-threshold* rational — there is no symmetric mirror.

All zero-axiom (no `propext`, `Classical` choice, `funext`, or compiled reflection): everything
is a finite `Nat` (in)equality on the concrete recursive `P`, in the style of the
calibration file it extends.
-/

namespace E213.Lib.Math.Logic.OmniscienceCostSharp

open E213.Lib.Math.Logic.RealDichotomyLLPO
  (P yf one yf_eq one_eq P_odd_exact P_eq_pow_of_noFire P_gt_pow_even mul_lt_mul_right_pos)
open E213.Lib.Math.Logic (parity)

/-! ## §1 — the upper bound: `2^{n+1}` certifies (boundary rational `= y_f`) -/

/-- ★★★ **Upper bound.**  For an odd fire at `n`, the denominator `2^{n+1}` with numerator
    `2^{n+1}−1` certifies: `one (2^{n+1}−1) (2^{n+1}) = false` (the rational is `< 1`) and
    `yf f (2^{n+1}−1) (2^{n+1}) = true` (it equals `y_f = 1 − 2^{-(n+1)}`, certified by the
    cut's `≤`). -/
theorem odd_cert_at_pow (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    one (2 ^ (n + 1) - 1) (2 ^ (n + 1)) = false ∧
      yf f (2 ^ (n + 1) - 1) (2 ^ (n + 1)) = true := by
  have hSpos : 0 < 2 ^ (n + 1) := Nat.pos_pow_of_pos _ (by decide)
  have hnS : n ≤ 2 ^ (n + 1) :=
    Nat.le_trans (Nat.le_succ n) (Nat.le_of_lt (E213.Meta.Nat.PureNat.lt_two_pow (n + 1)))
  have hidx : n + 1 + (2 ^ (n + 1) - n) = 2 ^ (n + 1) + 1 := by
    rw [Nat.add_right_comm n 1 (2 ^ (n + 1) - n), E213.Tactic.NatHelper.add_sub_of_le hnS]
  have hexact : P f (2 ^ (n + 1) + 1) + 2 ^ (2 ^ (n + 1) - n) = 2 ^ (2 ^ (n + 1) + 1) := by
    have h := P_odd_exact f n hfn hpar hbef haft (2 ^ (n + 1) - n)
    rw [hidx] at h; exact h
  have hexp : (2 ^ (n + 1) - n) + (n + 1) = 2 ^ (n + 1) + 1 := by
    rw [← Nat.add_assoc, E213.Tactic.NatHelper.sub_add_cancel hnS]
  have hpow : 2 ^ (2 ^ (n + 1) - n) * 2 ^ (n + 1) = 2 ^ (2 ^ (n + 1) + 1) := by
    rw [← E213.Meta.Nat.PureNat.pow_add, hexp]
  have step1 :
      P f (2 ^ (n + 1) + 1) * 2 ^ (n + 1) + 2 ^ (2 ^ (n + 1) + 1)
        = 2 ^ (2 ^ (n + 1) + 1) * 2 ^ (n + 1) :=
    calc P f (2 ^ (n + 1) + 1) * 2 ^ (n + 1) + 2 ^ (2 ^ (n + 1) + 1)
        = P f (2 ^ (n + 1) + 1) * 2 ^ (n + 1) + 2 ^ (2 ^ (n + 1) - n) * 2 ^ (n + 1) := by
          rw [← hpow]
      _ = (P f (2 ^ (n + 1) + 1) + 2 ^ (2 ^ (n + 1) - n)) * 2 ^ (n + 1) :=
          (E213.Tactic.NatHelper.add_mul _ _ _).symm
      _ = 2 ^ (2 ^ (n + 1) + 1) * 2 ^ (n + 1) := by rw [hexact]
  have hBle : 2 ^ (2 ^ (n + 1) + 1) ≤ 2 ^ (2 ^ (n + 1) + 1) * 2 ^ (n + 1) := by
    have h := Nat.mul_le_mul_left (2 ^ (2 ^ (n + 1) + 1)) hSpos
    rwa [Nat.mul_one] at h
  have step2 :
      2 ^ (2 ^ (n + 1) + 1) * (2 ^ (n + 1) - 1) + 2 ^ (2 ^ (n + 1) + 1)
        = 2 ^ (2 ^ (n + 1) + 1) * 2 ^ (n + 1) := by
    rw [E213.Tactic.NatHelper.mul_sub, Nat.mul_one, E213.Tactic.NatHelper.sub_add_cancel hBle]
  have hcancel :
      P f (2 ^ (n + 1) + 1) * 2 ^ (n + 1) + 2 ^ (2 ^ (n + 1) + 1)
        = 2 ^ (2 ^ (n + 1) + 1) * (2 ^ (n + 1) - 1) + 2 ^ (2 ^ (n + 1) + 1) := by
    rw [step1, step2]
  have hEq :
      P f (2 ^ (n + 1) + 1) * 2 ^ (n + 1)
        = 2 ^ (2 ^ (n + 1) + 1) * (2 ^ (n + 1) - 1) :=
    E213.Tactic.NatHelper.add_right_cancel hcancel
  refine ⟨?_, ?_⟩
  · rw [one_eq]
    exact decide_eq_false (Nat.not_le.mpr (Nat.sub_lt hSpos (by decide)))
  · rw [yf_eq]
    exact decide_eq_true (Nat.le_of_eq hEq)

/-! ## §2 — the lower bound: no denominator below `2^{n+1}` certifies -/

/-- ★★★ **Lower bound.**  For an odd fire at `n`, every resolution `k < 2^{n+1}` fails to
    certify: whatever `m` with `m/k < 1` (`one m k = false`), the cut reads `yf f m k =
    false`.  Equivalently: any rational with `y_f ≤ m/k < 1` has `k ≥ 2^{n+1}`. -/
theorem odd_no_cert_below (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    ∀ k m, k < 2 ^ (n + 1) → one m k = false → yf f m k = false := by
  intro k m hk hone
  rw [one_eq] at hone
  have hmk : m < k := Nat.not_le.mp (of_decide_eq_false hone)
  rw [yf_eq]
  rcases Nat.lt_or_ge k n with hkn | hkn
  · have hpe : P f (k + 1) = 2 ^ (k + 1) :=
      P_eq_pow_of_noFire f (k + 1)
        (fun i hi => hbef i (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hi) hkn))
    have hpos : 0 < 2 ^ (k + 1) := Nat.pos_pow_of_pos _ (by decide)
    apply decide_eq_false
    apply Nat.not_le.mpr
    rw [hpe, Nat.mul_comm (2 ^ (k + 1)) m, Nat.mul_comm (2 ^ (k + 1)) k]
    exact mul_lt_mul_right_pos hmk hpos
  · have hidx : n + 1 + (k - n) = k + 1 := by
      rw [Nat.add_right_comm n 1 (k - n), E213.Tactic.NatHelper.add_sub_of_le hkn]
    have hexact : P f (k + 1) + 2 ^ (k - n) = 2 ^ (k + 1) := by
      have h := P_odd_exact f n hfn hpar hbef haft (k - n)
      rw [hidx] at h; exact h
    have hPk : P f (k + 1) * k + 2 ^ (k - n) * k = 2 ^ (k + 1) * k := by
      rw [← E213.Tactic.NatHelper.add_mul, hexact]
    have hexp : (k - n) + (n + 1) = k + 1 := by
      rw [← Nat.add_assoc, E213.Tactic.NatHelper.sub_add_cancel hkn]
    have hpowk : 2 ^ (k - n) * 2 ^ (n + 1) = 2 ^ (k + 1) := by
      rw [← E213.Meta.Nat.PureNat.pow_add, hexp]
    have hA : 2 ^ (k - n) * k < 2 ^ (k + 1) := by
      rw [← hpowk, Nat.mul_comm (2 ^ (k - n)) k, Nat.mul_comm (2 ^ (k - n)) (2 ^ (n + 1))]
      exact mul_lt_mul_right_pos hk (Nat.pos_pow_of_pos _ (by decide))
    have hB : 2 ^ (k + 1) * m + 2 ^ (k + 1) ≤ 2 ^ (k + 1) * k := by
      have hexp2 : 2 ^ (k + 1) * (m + 1) = 2 ^ (k + 1) * m + 2 ^ (k + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [← hexp2]
      exact Nat.mul_le_mul_left (2 ^ (k + 1)) hmk
    have hcomb : 2 ^ (k + 1) * m + 2 ^ (k - n) * k < P f (k + 1) * k + 2 ^ (k - n) * k :=
      calc 2 ^ (k + 1) * m + 2 ^ (k - n) * k
            < 2 ^ (k + 1) * m + 2 ^ (k + 1) := Nat.add_lt_add_left hA _
        _ ≤ 2 ^ (k + 1) * k := hB
        _ = P f (k + 1) * k + 2 ^ (k - n) * k := hPk.symm
    apply decide_eq_false
    exact Nat.not_le.mpr (Nat.lt_of_add_lt_add_right hcomb)

/-! ## §3 — sharpness: the least certifying denominator is `2^{n+1}` -/

/-- `k` *certifies* (separates `y_f` strictly below `1`) if some `m/k` lies in `[y_f, 1)`. -/
def OddCertifies (f : Nat → Bool) (k : Nat) : Prop :=
  ∃ m, one m k = false ∧ yf f m k = true

/-- The witness from §1: `2^{n+1}` certifies. -/
theorem oddCertifies_pow (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    OddCertifies f (2 ^ (n + 1)) :=
  ⟨2 ^ (n + 1) - 1, odd_cert_at_pow f n hfn hpar hbef haft⟩

/-- The bound from §2: every certifying denominator is `≥ 2^{n+1}`. -/
theorem oddCertifies_lb (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    ∀ k, OddCertifies f k → 2 ^ (n + 1) ≤ k := by
  intro k hc
  obtain ⟨m, hone, hyf⟩ := hc
  rcases Nat.lt_or_ge k (2 ^ (n + 1)) with hlt | hge
  · have hf := odd_no_cert_below f n hfn hpar hbef haft k m hlt hone
    rw [hf] at hyf
    exact Bool.noConfusion hyf
  · exact hge

/-- ★★★ **Sharp omniscience cost.**  `2^{n+1}` is the least certifying denominator: it
    certifies, and no smaller resolution does.  The price of the LLPO-gated order decision
    on this instance is the exact, fire-index-indexed denominator `2^{n+1}`. -/
theorem odd_min_cert_denom (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = true)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    OddCertifies f (2 ^ (n + 1)) ∧ (∀ k, OddCertifies f k → 2 ^ (n + 1) ≤ k) :=
  ⟨oddCertifies_pow f n hfn hpar hbef haft, oddCertifies_lb f n hfn hpar hbef haft⟩

/-! ## §4 — the asymmetry: the dual (even) separation is cheap -/

/-- **The even side is cheap.**  For an even fire at `n` (`y_f = 1 + 2^{-(n+1)} > 1`), the
    threshold rational `1 = (n+1)/(n+1)` already lies in `[1, y_f)`, so it refutes
    `y_f ≤ 1` at denominator `n+1`: `one (n+1) (n+1) = true` while
    `yf f (n+1) (n+1) = false`.  No exponential resolution is needed — the cost is **not**
    symmetric with the odd case. -/
theorem even_cert_cheap (f : Nat → Bool) (n : Nat)
    (hfn : f n = true) (hpar : parity n = false)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    one (n + 1) (n + 1) = true ∧ yf f (n + 1) (n + 1) = false := by
  refine ⟨?_, ?_⟩
  · rw [one_eq]; exact decide_eq_true (Nat.le_refl _)
  · rw [yf_eq]
    exact decide_eq_false
      (Nat.not_le.mpr (mul_lt_mul_right_pos (P_gt_pow_even f n hfn hpar hbef haft 1)
        (Nat.succ_pos n)))

/-- The even certifying denominator `n+1` is strictly below the odd minimal denominator
    `2^{n+1}`: the omniscience cost of the dichotomy is one-sided. -/
theorem cost_asymmetric (n : Nat) : n + 1 < 2 ^ (n + 1) :=
  E213.Meta.Nat.PureNat.lt_two_pow (n + 1)

end E213.Lib.Math.Logic.OmniscienceCostSharp
