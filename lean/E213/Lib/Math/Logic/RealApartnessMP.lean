import E213.Lib.Math.Logic.Omniscience
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# vein-C CALIBRATION: real apartness ⟺ Markov's Principle (MP)

The companion `RealDichotomyLLPO` pinned the real **sign** decision = LLPO.
This file pins the third leg of the real-decision triad: real **apartness** =
**MP**.

A real `x` that is merely *not equal* to `0` (`¬ cutEq x zero`) is **apart**
from `0` — it carries a *located positive distance*: an explicit resolution at
which `x` reads strictly above `0` — exactly when Markov's Principle holds.  The
located resolution is what makes the fire-search *bounded*; that bounded search
for the `Nat` witness IS the MP content.

## The encoding (all one sign — MP extracts the witness)

Given `f : Nat → Bool`, build `x_f = Σ_n [f n]·2^{-(n+1)}` (non-negative).
Layer-`n` numerator over denominator `2^n`:

  `Q f 0 = 0`,  `Q f (n+1) = 2·Q f n + (if f n then 1 else 0)`.

`x_f m k := constCut (Q f (k+1)) (2^(k+1)) m k`, value `Q f (k+1) / 2^(k+1)`.

`zero = constCut 0 1` reads `true` at every `(m,k)` (`0 ≤ m` always).

  * No fire ⟹ `Q f = 0` ⟹ `cutEq x_f zero`.
  * A fire at `n` ⟹ `Q f (k+1) ≥ 1` for `k ≥ n` ⟹ the probe `(0, n+1)` reads
    `false` (`x_f` is *not* `≤ 0` there) — a located positive distance
    (`apart_of_fire`).
  * **`mp_of_realApartness`**: a located probe `(0, k+1)` reading `false` forces
    `Q f (k+2) > 0`, hence a fire *below `k+2`* — found by a bounded decidable
    scan.  That bounded extraction is Markov's principle.

## Apartness definition (cut-bit witness form)

`Apart x := ∃ k, x 0 (k+1) = false` — "`x` is *not* `≤ 0/(k+1) = 0` at the
explicit resolution `k+1`", i.e. `x > 0` witnessed at a concrete probe.  The
`Nat`-fire witness drives it directly.
-/

namespace E213.Lib.Math.Logic.RealApartnessMP

open E213.Lib.Math.Logic (MP)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutLe cutEq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — the partial-sum numerator `Q f n` over denominator `2^n` -/

/-- Layer-`n` numerator of `x_f` over denominator `2^n`.  Doubling the
    denominator doubles the numerator; a fire at index `n` adds `+1`. -/
def Q (f : Nat → Bool) : Nat → Nat
  | 0     => 0
  | n + 1 => 2 * Q f n + (if f n = true then 1 else 0)

/-- The encoded real `x_f` as a corpus cut: at resolution `k` it reads the
    layer-`(k+1)` approximant `Q f (k+1) / 2^(k+1)`. -/
def xf (f : Nat → Bool) : Nat → Nat → Bool :=
  fun m k => constCut (Q f (k + 1)) (2 ^ (k + 1)) m k

/-- The constant `0` as a cut: `constCut 0 1`. -/
def zero : Nat → Nat → Bool := constCut 0 1

/-- `xf f m k = decide (Q f (k+1) * k ≤ 2^(k+1) * m)`. -/
theorem xf_eq (f : Nat → Bool) (m k : Nat) :
    xf f m k = decide (Q f (k + 1) * k ≤ 2 ^ (k + 1) * m) := rfl

/-- `zero m k = true` for every `(m, k)` (since `0 ≤ m`). -/
theorem zero_true (m k : Nat) : zero m k = true := by
  show decide (0 * k ≤ 1 * m) = true
  apply decide_eq_true
  rw [Nat.zero_mul]
  exact Nat.zero_le _

/-! ## §2 — no fire below `B` ⟹ `Q f B = 0`; a positive `Q` locates a fire -/

/-- No fire below `B` keeps the numerator at `0`. -/
theorem Q_eq_zero_of_noFire (f : Nat → Bool) :
    ∀ B, (∀ n, n < B → f n = false) → Q f B = 0
  | 0,     _ => rfl
  | B + 1, h => by
    show 2 * Q f B + (if f B = true then 1 else 0) = 0
    have hfB : f B = false := h B (Nat.lt_succ_self B)
    rw [hfB]
    show 2 * Q f B + 0 = 0
    rw [Nat.add_zero,
        Q_eq_zero_of_noFire f B (fun n hn => h n (Nat.lt_trans hn (Nat.lt_succ_self B))),
        Nat.mul_zero]

/-- **Bounded fire search**: a positive numerator at layer `B` locates a fire
    below `B`.  Pure decidable scan (induction on `B`, `cases f B`); the located
    `B` from apartness bounds this search — the MP witness extraction. -/
theorem fire_of_Q_pos (f : Nat → Bool) :
    ∀ B, 0 < Q f B → ∃ n, f n = true
  | 0,     h => absurd h (Nat.not_lt_zero 0)
  | B + 1, h => by
    -- Q f (B+1) = 2 * Q f B + (if f B then 1 else 0)
    cases hfB : f B with
    | true => exact ⟨B, hfB⟩
    | false =>
      -- Q f (B+1) = 2 * Q f B, so 0 < Q f B
      have hQ : Q f (B + 1) = 2 * Q f B := by
        show 2 * Q f B + (if f B = true then 1 else 0) = 2 * Q f B
        rw [hfB]; show 2 * Q f B + 0 = 2 * Q f B; rw [Nat.add_zero]
      rw [hQ] at h
      have hpos : 0 < Q f B := by
        cases hQB : Q f B with
        | zero => rw [hQB, Nat.mul_zero] at h; exact absurd h (by decide)
        | succ q => exact Nat.succ_pos q
      exact fire_of_Q_pos f B hpos

/-- After a fire at `n`, the numerator is `≥ 1` from layer `n+1` onward
    (`1 ≤ Q f (n+1+t)`). -/
theorem one_le_Q_after_fire (f : Nat → Bool) (n : Nat) (hfn : f n = true) :
    ∀ t, 1 ≤ Q f (n + 1 + t)
  | 0 => by
    show 1 ≤ Q f (n + 1)
    show 1 ≤ 2 * Q f n + (if f n = true then 1 else 0)
    rw [hfn]
    show 1 ≤ 2 * Q f n + 1
    exact Nat.le_add_left 1 (2 * Q f n)
  | t + 1 => by
    show 1 ≤ Q f (n + 1 + t + 1)
    show 1 ≤ 2 * Q f (n + 1 + t) + (if f (n + 1 + t) = true then 1 else 0)
    have ih : 1 ≤ Q f (n + 1 + t) := one_le_Q_after_fire f n hfn t
    have h2 : 1 ≤ 2 * Q f (n + 1 + t) :=
      Nat.le_trans ih (Nat.le_trans (Nat.le_of_eq (Nat.one_mul _).symm)
        (Nat.mul_le_mul_right _ (by decide)))
    exact Nat.le_trans h2 (Nat.le_add_right _ _)

/-! ## §3 — `Apart`: a located positive distance from `0` (cut-bit witness) -/

/-- **Located positive distance from `0`**: an explicit resolution `k+1` at
    which `x` reads `false` (i.e. `x` is *not* `≤ 0`, so `x > 0` there). -/
def Apart (x : Nat → Nat → Bool) : Prop :=
  ∃ k, x 0 (k + 1) = false

/-- **`apart_of_fire`** — an explicit fire at `n` gives the located distance
    witnessed at resolution `n+1` (`x_f 0 (n+1) = false`).  ∅-axiom, the
    constructive core: the fire makes `Q f (n+2) ≥ 1`, so `x_f` is strictly
    above `0/(n+1)`. -/
theorem apart_of_fire (f : Nat → Bool) (n : Nat) (hfn : f n = true) :
    Apart (xf f) := by
  refine ⟨n, ?_⟩
  rw [xf_eq]
  apply decide_eq_false
  -- goal: ¬ (Q f (n+2) * (n+1) ≤ 2^(n+2) * 0)
  rw [Nat.mul_zero]
  apply Nat.not_le.mpr
  -- 0 < Q f (n+2) * (n+1)
  have hQ : 1 ≤ Q f (n + 1 + 1) := one_le_Q_after_fire f n hfn 1
  exact Nat.mul_pos (Nat.lt_of_lt_of_le (by decide) hQ) (Nat.succ_pos n)

/-! ## §4 — `cutEq` ⟺ no fire (the non-equality ↔ fire connection) -/

/-- `cutEq x_f zero ⟹ ∀ n, f n = false` — pointwise: a fire at any `n` would
    make `x_f 0 (n+1) = false`, contradicting `cutEq`'s pointwise `true`. -/
theorem noFire_of_cutEq (f : Nat → Bool) (heq : cutEq (xf f) zero) :
    ∀ n, f n = false := by
  intro n
  cases hfn : f n with
  | false => rfl
  | true =>
    -- fire at n ⟹ apart witness at n ⟹ xf f 0 (n+1) = false, but cutEq says true
    obtain ⟨k, hk⟩ := apart_of_fire f n hfn
    -- here k = n (from apart_of_fire), but we only need the contradiction at k
    have htrue : xf f 0 (k + 1) = zero 0 (k + 1) := heq 0 (k + 1)
    rw [zero_true] at htrue
    rw [hk] at htrue
    exact Bool.noConfusion htrue

/-- **`notEq_of_not_all_false`** (the `¬ cutEq ⟸ ¬∀false` half of
    `notEq_iff_fire`): if `f` is not everywhere-false, `x_f` is not equal to
    `0`.  Contrapositive of `noFire_of_cutEq` — purely negational, no witness
    extracted yet. -/
theorem notEq_of_not_all_false (f : Nat → Bool) (hnot : ¬ (∀ n, f n = false)) :
    ¬ cutEq (xf f) zero :=
  fun heq => hnot (noFire_of_cutEq f heq)

/-- **`fire_of_notEq`** (the `¬ cutEq ⟹ ∃ fire` half of `notEq_iff_fire`):
    a located disequality `Apart x_f` gives an explicit fire.  Combined with
    `apart_of_fire`, `Apart (xf f) ↔ ∃ n, f n = true`. -/
theorem fire_of_apart (f : Nat → Bool) (hap : Apart (xf f)) :
    ∃ n, f n = true := by
  obtain ⟨k, hk⟩ := hap
  -- xf f 0 (k+1) = false ⟹ ¬ (Q f (k+2) * (k+1) ≤ 0) ⟹ 0 < Q f (k+2)
  rw [xf_eq] at hk
  have hk' : ¬ (Q f (k + 1 + 1) * (k + 1) ≤ 2 ^ (k + 1 + 1) * 0) := of_decide_eq_false hk
  rw [Nat.mul_zero] at hk'
  have hpos_prod : 0 < Q f (k + 1 + 1) * (k + 1) := Nat.not_le.mp hk'
  -- 0 < Q f (k+2)  (else the product is 0)
  have hpos : 0 < Q f (k + 1 + 1) := by
    cases hQ : Q f (k + 1 + 1) with
    | zero => rw [hQ, Nat.zero_mul] at hpos_prod; exact absurd hpos_prod (by decide)
    | succ q => exact Nat.succ_pos q
  exact fire_of_Q_pos f (k + 1 + 1) hpos

/-! ## §5 — the calibration: real apartness ⟺ MP -/

/-- ★★★ **MP from real apartness** — the forward calibration.

    Hypothesis: every real *not equal* to `0` is *apart* from `0` (carries a
    located positive distance).  Then Markov's Principle holds.

    Given `f` with `¬ (∀ n, f n = false)`, `x_f` is not equal to `0`
    (`notEq_of_not_all_false`, purely negational); the apartness hypothesis
    upgrades this to a *located* distance `Apart (xf f)` — an explicit
    resolution at which `x_f > 0`; that located probe **bounds** the fire-search
    (`fire_of_apart` runs the decidable scan `fire_of_Q_pos`), yielding the
    explicit witness `∃ n, f n = true`.  ∅-axiom: apartness is a `Prop`
    hypothesis, never an axiom. -/
theorem mp_of_realApartness
    (hap : ∀ x : Nat → Nat → Bool, ¬ cutEq x zero → Apart x) : MP :=
  fun f hnot =>
    fire_of_apart f (hap (xf f) (notEq_of_not_all_false f hnot))

/-- ★★ **Real apartness from MP** (the converse — the easier direction).
    `MP` on `f` extracts the fire `∃ n, f n = true`; `apart_of_fire` turns that
    fire into the located distance `Apart (xf f)`.  Together with
    `mp_of_realApartness` this is the two-sided calibration:
    *the apartness decision on the encoded reals is exactly MP*. -/
theorem realApartness_of_mp (hmp : MP) (f : Nat → Bool)
    (hne : ¬ cutEq (xf f) zero) : Apart (xf f) := by
  -- ¬ cutEq ⟹ ¬ (∀ n, f n = false)  (else cutEq holds via cutEq_of_noFire)
  have hnot : ¬ (∀ n, f n = false) := by
    intro hall
    exact hne (by
      intro m k
      rw [zero_true, xf_eq]
      apply decide_eq_true
      rw [Q_eq_zero_of_noFire f (k + 1) (fun n _ => hall n), Nat.zero_mul]
      exact Nat.zero_le _)
  obtain ⟨n, hn⟩ := hmp f hnot
  exact apart_of_fire f n hn

end E213.Lib.Math.Logic.RealApartnessMP
