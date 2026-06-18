import E213.Lib.Math.Logic.RealApartnessMP
import E213.Lib.Math.Logic.OmniscienceCostSharp
import E213.Meta.Nat.PureNat

/-!
# ApartnessCostSharp — the boundary omniscience cost, and the quantitative ledger

`OmniscienceCostSharp` made the LLPO sign-decision cost sharp: for an odd fire at `n`,
certifying `y_f` strictly below the **interior** threshold `1` costs exactly denominator
`2^{n+1}` (and the dual even side is cheap — the threshold rational `1` itself separates).

This file gives the **boundary** mirror.  In the apartness/MP encoding (`RealApartnessMP`)
the threshold is `0`, and `0 = 0/k` always lies on the cheap side of a positive value, so
separation never pays the exponential gap-squeeze:

> ★★★ `apart_min_sep_denom` — for a single fire at `n` (`n ≥ 1`, no earlier fire), the least
> denominator separating `x_f` from `0` is exactly **`n`** (with numerator `0`): UB
> `sep_at_fire` (`Q f(n+1) ≥ 1`, so `x_f` reads apart at resolution `n`), LB
> `no_sep_below_fire` (every `k < n` has `Q f(k+1) = 0`, reading `true` = not apart).

So the certifying cost is **`Θ(2^{n})` exactly when the value approaches an *interior*
threshold from its excluded side** (a sub-threshold rational squeezed into a gap of width
`2^{-(n+1)}`), and **`Θ(n)` when the threshold sits on the cheap side** (`0`, or `1` from
below).  The unifying datum is the threshold's position, not the principle's name.

> ★★ `omniscience_cost_ledger` — on one bit-stream `f` (single fire at `n`, odd): read as the
> LLPO real, the certifying denominator is `2^{n+1}` (interior); read as the apartness real,
> it is `n` (boundary); and `n < 2^{n+1}` — the *same* `lt_two_pow` lemma that witnesses
> LLPO's one-sidedness witnesses the boundary-vs-interior gap.

Honest scope: the underlying inequality (a rational in `[1−2^{-m},1)` needs denominator
`≥ 2^m`; one in `[0,ε)` needs denominator `1`) is elementary.  The contribution is its sharp,
two-sided, ∅-axiom packaging as a *per-principle resolution-growth signature* on a common
instance family — a resource annotation refining the located reading of LPO/LLPO/WLPO/MP by
threshold position, not a new separation or a Weihrauch-degree result.

All zero-axiom.
-/

namespace E213.Lib.Math.Logic.ApartnessCostSharp

open E213.Lib.Math.Logic.RealApartnessMP
  (Q xf zero xf_eq Q_eq_zero_of_noFire one_le_Q_after_fire)
open E213.Lib.Math.Logic.OmniscienceCostSharp (OddCertifies odd_min_cert_denom)
open E213.Lib.Math.Logic (parity)

/-! ## §1 — separation from the boundary threshold `0` -/

/-- `k` *separates* `x_f` from `0`: the trivial probe rational `0 = 0/k` already reads
    `x_f` apart (`xf f 0 k = false`, i.e. `x_f > 0` certified at resolution `k`). -/
def SepFromZero (f : Nat → Bool) (k : Nat) : Prop := xf f 0 k = false

/-- ★★ **Upper bound.**  A fire at `n` (`n ≥ 1`) separates at denominator `n`: the layer
    numerator `Q f(n+1) ≥ 1`, so `Q f(n+1)·n > 0` and the cut reads `false` (apart). -/
theorem sep_at_fire (f : Nat → Bool) (n : Nat) (hfn : f n = true) (hn : 1 ≤ n) :
    SepFromZero f n := by
  show xf f 0 n = false
  rw [xf_eq, Nat.mul_zero]
  apply decide_eq_false
  apply Nat.not_le.mpr
  exact Nat.mul_pos (Nat.lt_of_lt_of_le (by decide) (one_le_Q_after_fire f n hfn 0)) hn

/-- ★★ **Lower bound.**  For a single fire at `n` (no earlier fire), every `k < n` fails to
    separate: `Q f(k+1) = 0` (numerator unseen), so `x_f` reads `true` (not apart). -/
theorem no_sep_below_fire (f : Nat → Bool) (n : Nat)
    (hbef : ∀ i, i < n → f i = false) :
    ∀ k, k < n → xf f 0 k = true := by
  intro k hk
  rw [xf_eq]
  apply decide_eq_true
  have hQ : Q f (k + 1) = 0 :=
    Q_eq_zero_of_noFire f (k + 1)
      (fun i hi => hbef i (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hi) hk))
  rw [hQ, Nat.zero_mul]
  exact Nat.zero_le _

/-- ★★★ **Sharp boundary cost.**  For a single fire at `n` (`n ≥ 1`), `n` is the least
    separating denominator: it separates, and no smaller resolution does.  The price of the
    apartness/MP located decision is *linear* in the fire index — the boundary mirror of
    LLPO's exponential interior cost. -/
theorem apart_min_sep_denom (f : Nat → Bool) (n : Nat) (hfn : f n = true) (hn : 1 ≤ n)
    (hbef : ∀ i, i < n → f i = false) :
    SepFromZero f n ∧ (∀ k, SepFromZero f k → n ≤ k) := by
  refine ⟨sep_at_fire f n hfn hn, ?_⟩
  intro k hk
  have hk' : xf f 0 k = false := hk
  rcases Nat.lt_or_ge k n with hlt | hge
  · rw [no_sep_below_fire f n hbef k hlt] at hk'
    exact Bool.noConfusion hk'
  · exact hge

/-! ## §2 — the quantitative ledger: interior vs boundary on one instance -/

/-- ★★ **Quantitative omniscience ledger.**  On one bit-stream `f` (single odd fire at `n`,
    `n ≥ 1`): read as the **interior**-threshold LLPO real, the least certifying denominator
    is `2^{n+1}` (exponential, `odd_min_cert_denom`); read as the **boundary**-threshold
    apartness real, it is `n` (linear, `apart_min_sep_denom`); and `n < 2^{n+1}`.  The
    located reading of the omniscience principles is refined by the sharp resolution-growth
    signature, indexed by threshold position. -/
theorem omniscience_cost_ledger (f : Nat → Bool) (n : Nat) (hfn : f n = true)
    (hpar : parity n = true) (hn : 1 ≤ n)
    (hbef : ∀ i, i < n → f i = false) (haft : ∀ i, n < i → f i = false) :
    (OddCertifies f (2 ^ (n + 1)) ∧ (∀ k, OddCertifies f k → 2 ^ (n + 1) ≤ k))
  ∧ (SepFromZero f n ∧ (∀ k, SepFromZero f k → n ≤ k))
  ∧ n < 2 ^ (n + 1) :=
  ⟨odd_min_cert_denom f n hfn hpar hbef haft,
   apart_min_sep_denom f n hfn hn hbef,
   Nat.lt_trans (Nat.lt_succ_self n) (E213.Meta.Nat.PureNat.lt_two_pow (n + 1))⟩

end E213.Lib.Math.Logic.ApartnessCostSharp
