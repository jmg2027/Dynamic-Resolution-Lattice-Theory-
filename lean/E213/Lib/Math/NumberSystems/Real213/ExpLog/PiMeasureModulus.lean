import E213.Lib.Math.NumberSystems.Real213.ExpLog.PiCut
import E213.Lib.Math.NumberSystems.Real213.Modulus.BracketModulus
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
import E213.Meta.Nat.PolyNatMTactic

/-!
# PiMeasureModulus — π/2 (and π) carry a conditional degree-`s` modulus

The conditional measure-modulus schema (modulus-degree ladder rung 2), at its
first named instance.  The Wallis lower fold `W_n = wallisNum n / wallisDen n`
gets a **decreasing upper companion** `U_n = W_n·(2n+2)/(2n+1)` (`upNum/upDen`,
`up_mono`), so π/2 sits in a per-layer shrinking bracket `(W_n, U_n)` of width
`W_n/(2n+1) ≤ 2/(2n+1)` — the Wallis `1/n` rate made a two-sided sandwich.

`PiHalfMeasure C s` is the **effective irrationality measure of π/2 relative to
this bracket**, in pure ℕ form: any probe `m/k` still strictly inside the
layer-`n` bracket forces the width to be at least `1/(C·k^s)`
(`(2n+1)·wallisDen n ≤ C·(wallisNum n·k^s)`).  Classically this is
`|π/2 − m/k| ≥ 1/(C·k^s)`, i.e. an effective `μ(π/2) ≤ s`; the best known is
`μ(π) ≤ 7.103` (Zeilberger–Zudilin 2020), so the expected true instance is
`s = 8` with some constant — **not formalized here**: the analytic cost is
isolated in this single arithmetic hypothesis, and everything downstream is
∅-axiom constructed.

  * width ≥ `1/(C·k^s)` + width rate `≤ 2/(2n+1)` ⟹ exclusion depth
    `n ≤ C·k^s` (`measure_exclusion`, via `wallisNum n ≤ 2·wallisDen n` from
    `wallis_upper_inv`);
  * `BracketModulus.bracket_total_modulus` then constructs the total modulus
    **`N(m,k) = C·k^s + 2`** for π/2 (`halfPi_measure_modulus`) and
    `N(m,k) = C·(2k)^s + 2` for π (`pi_measure_modulus`).

π thereby moves from "completion modulus as opaque hypothesis" (the π-posture
of `PiCut`/`AbCutSeq`) to **"conditional degree-`s` modulus"**: the hypothesis
is one named distance inequality, the modulus shape `C·k^s + 2` is a theorem.
Wallis itself stays rate-free at every *unconditional* grade (the graded
generator does not apply: the tail `~1/n` overtakes every scheduled quantum);
the measure is exactly what the presentation is missing, and this file prices
it.  All zero-axiom (conditionally on nothing — the hypothesis is a binder).
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.PiMeasureModulus
open E213.Lib.Math.NumberSystems.Real213.Modulus

open E213.Lib.Math.Analysis.Cauchy.WallisSeq
  (wallisNum wallisDen wallisNum_pos wallisDen_pos kk_lt_4_kp1_sq wallis_upper_inv)
open E213.Lib.Math.NumberSystems.Real213.Modulus.BracketModulus (Inside bracket_total_modulus)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.PiCut (halfPiCut halfPiCut_eq piCut)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (HtelS)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
  (DominatesS htelS_iff_dominatesS)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_left)
open E213.Tactic.NatHelper (le_of_mul_le_mul_right)

/-! ## §1 — the decreasing upper companion `U_n = W_n·(2n+2)/(2n+1)` -/

/-- Upper companion numerator: `wallisNum n · (2n+2)`. -/
def upNum (n : Nat) : Nat := wallisNum n * (2*n+2)

/-- Upper companion denominator: `wallisDen n · (2n+1)`. -/
def upDen (n : Nat) : Nat := wallisDen n * (2*n+1)

theorem upDen_pos (n : Nat) : 1 ≤ upDen n :=
  Nat.mul_pos (wallisDen_pos n) (Nat.zero_lt_succ _)

/-- The Wallis fold is strictly increasing, cross-multiplied
    (`4(n+1)² > (2n+1)(2n+3)`). -/
theorem wallis_step (n : Nat) :
    wallisNum n * wallisDen (n+1) < wallisNum (n+1) * wallisDen n := by
  show wallisNum n * (wallisDen n * ((2*n+1) * (2*n+3)))
      < wallisNum n * (4 * (n+1) * (n+1)) * wallisDen n
  have e1 : wallisNum n * (wallisDen n * ((2*n+1) * (2*n+3)))
      = (wallisNum n * wallisDen n) * ((2*n+1) * (2*n+3)) := by ring_nat
  have e2 : wallisNum n * (4 * (n+1) * (n+1)) * wallisDen n
      = (wallisNum n * wallisDen n) * (4 * ((n+1) * (n+1))) := by ring_nat
  rw [e1, e2]
  exact nat_mul_lt_mul_left
    (Nat.mul_pos (wallisNum_pos n) (wallisDen_pos n)) (kk_lt_4_kp1_sq n)

/-- ★ **The upper companion is non-increasing**: `U_{n+1} ≤ U_n`.  After the
    recursions, the coefficient comparison is the exact identity
    `4(n+1)²(2n+4)(2n+1) + 2(n+1)(2n+1) = (2n+2)(2n+1)(2n+3)²`. -/
theorem up_mono (n : Nat) : upNum (n+1) * upDen n ≤ upNum n * upDen (n+1) := by
  show (wallisNum n * (4 * (n+1) * (n+1)) * (2*(n+1)+2)) * (wallisDen n * (2*n+1))
      ≤ (wallisNum n * (2*n+2)) * (wallisDen n * ((2*n+1) * (2*n+3)) * (2*(n+1)+1))
  have e1 : (wallisNum n * (4 * (n+1) * (n+1)) * (2*(n+1)+2)) * (wallisDen n * (2*n+1))
      = (wallisNum n * wallisDen n)
          * (4 * (n+1) * (n+1) * ((2*n+4) * (2*n+1))) := by ring_nat
  have e2 : (wallisNum n * (2*n+2)) * (wallisDen n * ((2*n+1) * (2*n+3)) * (2*(n+1)+1))
      = (wallisNum n * wallisDen n)
          * ((2*n+2) * ((2*n+1) * ((2*n+3) * (2*n+3)))) := by ring_nat
  have hcoef : 4 * (n+1) * (n+1) * ((2*n+4) * (2*n+1))
      ≤ (2*n+2) * ((2*n+1) * ((2*n+3) * (2*n+3))) := by
    have hid : 4 * (n+1) * (n+1) * ((2*n+4) * (2*n+1)) + 2 * (n+1) * (2*n+1)
        = (2*n+2) * ((2*n+1) * ((2*n+3) * (2*n+3))) := by ring_nat
    rw [← hid]
    exact Nat.le_add_right _ _
  rw [e1, e2]
  exact Nat.mul_le_mul_left _ hcoef

/-- Per-layer sandwich `W_n < U_n` (the width `W_n/(2n+1)` is positive). -/
theorem wallis_sandwich (n : Nat) : wallisNum n * upDen n < upNum n * wallisDen n := by
  show wallisNum n * (wallisDen n * (2*n+1)) < (wallisNum n * (2*n+2)) * wallisDen n
  have e1 : wallisNum n * (wallisDen n * (2*n+1))
      = (wallisNum n * wallisDen n) * (2*n+1) := by ring_nat
  have e2 : (wallisNum n * (2*n+2)) * wallisDen n
      = (wallisNum n * wallisDen n) * (2*n+2) := by ring_nat
  rw [e1, e2]
  exact nat_mul_lt_mul_left
    (Nat.mul_pos (wallisNum_pos n) (wallisDen_pos n)) (Nat.lt_succ_self _)

/-- `W_n ≤ 2` in cross form, from `wallis_upper_inv` (cancel `2n+1`). -/
theorem wallisNum_le_two_den (n : Nat) : wallisNum n ≤ 2 * wallisDen n := by
  have h1 : wallisNum n * (2*n+1) ≤ (4*n+1) * wallisDen n := wallis_upper_inv n
  have h2 : (4*n+1) * wallisDen n ≤ (4*n+2) * wallisDen n :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  have e : (4*n+2) * wallisDen n = (2 * wallisDen n) * (2*n+1) := by ring_nat
  exact le_of_mul_le_mul_right (Nat.zero_lt_succ _)
    (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_of_eq e)))

/-! ## §2 — the measure hypothesis and its exclusion depth -/

/-- **Effective irrationality measure of π/2, Wallis-bracket form.**  Any probe
    `m/k` strictly inside the layer-`n` bracket `(W_n, U_n)` forces the bracket
    width `W_n/(2n+1)` to be at least `1/(C·k^s)`.  Classically:
    `|π/2 − m/k| ≥ 1/(C·k^s)` — an effective `μ(π/2) ≤ s`.  This single
    arithmetic inequality is the entire analytic cost of π's modulus. -/
def PiHalfMeasure (C s : Nat) : Prop :=
  ∀ m k n, 1 ≤ k → Inside wallisNum wallisDen upNum upDen m k n →
    (2*n+1) * wallisDen n ≤ C * (wallisNum n * k^s)

/-- ★★ **Measure ⟹ exclusion depth `C·k^s`.**  A probe still inside at layer
    `n` has width ≥ `1/(C·k^s)` (measure) while the width is ≤ `2/(2n+1)`
    (`wallisNum_le_two_den`), so `2n+1 ≤ 2C·k^s`, i.e. `n ≤ C·k^s`. -/
theorem measure_exclusion (C s : Nat) (hμ : PiHalfMeasure C s) :
    ∀ m k n, 1 ≤ k → Inside wallisNum wallisDen upNum upDen m k n →
      n ≤ C * k^s := by
  intro m k n hk hin
  have h1 : (2*n+1) * wallisDen n ≤ C * (wallisNum n * k^s) := hμ m k n hk hin
  have h2 : C * (wallisNum n * k^s) ≤ C * (2 * wallisDen n * k^s) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (wallisNum_le_two_den n))
  have e : C * (2 * wallisDen n * k^s) = (2 * C * k^s) * wallisDen n := by ring_nat
  have h4 : 2*n+1 ≤ 2 * C * k^s :=
    le_of_mul_le_mul_right (wallisDen_pos n)
      (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_of_eq e)))
  rcases Nat.lt_or_ge n (C * k^s + 1) with h | h
  · exact Nat.le_of_lt_succ h
  · have h5 : 2 * (C * k^s + 1) + 1 ≤ 2*n+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1
    have e2 : 2 * (C * k^s + 1) + 1 = 2 * C * k^s + 3 := by ring_nat
    have habs : 2 * C * k^s + 3 ≤ 2 * C * k^s :=
      Nat.le_trans (Nat.le_of_eq e2.symm) (Nat.le_trans h5 h4)
    exact absurd
      (Nat.le_trans (Nat.add_le_add_left (by decide : (1:Nat) ≤ 3) _) habs)
      (Nat.not_succ_le_self _)

/-! ## §3 — the conditional moduli -/

/-- ★★★ **π/2's conditional total modulus.**  Under `PiHalfMeasure C s`, the
    Wallis cut of π/2 is constant past **`N(m,k) = C·k^s + 2`** — constructed,
    ∅-axiom, with the analytic cost isolated in the one measure hypothesis. -/
theorem halfPi_measure_modulus (C s : Nat) (hμ : PiHalfMeasure C s)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → halfPiCut i m k = halfPiCut j m k := by
  obtain ⟨N, hN⟩ := bracket_total_modulus upDen_pos wallis_step up_mono
    wallis_sandwich (fun k => C * k^s) (measure_exclusion C s hμ) m k hk
  exact ⟨N, fun i j hi hj => by
    rw [halfPiCut_eq, halfPiCut_eq]
    exact hN i j hi hj⟩

/-- ★★★ **π's conditional total modulus** (`N(m,k) = C·(2k)^s + 2`): the
    doubling `piCut n m k = halfPiCut n m (2k)` transports the schema.
    π is conditionally a degree-`s` modulus real — rung 2 of the
    modulus-degree ladder, first named instance. -/
theorem pi_measure_modulus (C s : Nat) (hμ : PiHalfMeasure C s)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → piCut i m k = piCut j m k := by
  have h2k : 1 ≤ 2 * k := Nat.le_trans hk (Nat.le_mul_of_pos_left k (by decide))
  obtain ⟨N, hN⟩ := halfPi_measure_modulus C s hμ m (2*k) h2k
  exact ⟨N, fun i j hi hj => hN i j hi hj⟩

/-! ## §4 — the Wallis pointing is beyond every rung (the unconditional negative) -/

/-- **π/2's Wallis cross-determinant is the full product** `W_n = a_n·d_n`
    (`(2n+1)(2n+3) + 1 = 4(n+1)²`).  This is *why* the presentation's
    divergence depth is `6` (`DepthPiQuartic.piRatio_polyDepth`: the ratio
    `W_{n+1}/W_n = 4(n+1)²(2n+1)(2n+3)` is the degree-4 polynomial) — and why
    no schedule can absorb it. -/
theorem wallis_cross_det (n : Nat) :
    wallisNum (n+1) * wallisDen n
      = wallisNum n * wallisDen (n+1) + wallisNum n * wallisDen n := by
  show wallisNum n * (4 * (n+1) * (n+1)) * wallisDen n
      = wallisNum n * (wallisDen n * ((2*n+1) * (2*n+3)))
        + wallisNum n * wallisDen n
  ring_nat

theorem wallisNum_ge_four : ∀ n, 1 ≤ n → 4 ≤ wallisNum n
  | 0, h => absurd h (by decide)
  | 1, _ => by decide
  | n+2, _ => by
      have ih := wallisNum_ge_four (n+1) (Nat.succ_le_succ (Nat.zero_le n))
      show 4 ≤ wallisNum (n+1) * (4 * (n+2) * (n+2))
      exact Nat.le_trans ih (Nat.le_mul_of_pos_right _
        (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.zero_lt_succ _))
          (Nat.zero_lt_succ _)))

/-- From layer 2 on, the Wallis numerator passes the denominator-growth
    quadratic: `(2n+1)(2n+3) < wallisNum n`. -/
theorem quad_lt_wallisNum : ∀ n, 2 ≤ n → (2*n+1) * (2*n+3) < wallisNum n
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | m+2, _ => by
      have h4 : 4 ≤ wallisNum (m+1) :=
        wallisNum_ge_four (m+1) (Nat.succ_le_succ (Nat.zero_le m))
      show (2*(m+2)+1) * (2*(m+2)+3) < wallisNum (m+1) * (4 * (m+2) * (m+2))
      have h1 : (2*(m+2)+1) * (2*(m+2)+3) < 4 * ((m+3) * (m+3)) :=
        kk_lt_4_kp1_sq (m+2)
      have hb : m+3 ≤ 2*(m+2) := by
        have e : 2*(m+2) = (m+3) + (m+1) := by ring_nat
        rw [e]; exact Nat.le_add_right _ _
      have h2 : 4 * ((m+3) * (m+3)) ≤ 4 * (4 * (m+2) * (m+2)) := by
        have e : (2*(m+2)) * (2*(m+2)) = 4 * (m+2) * (m+2) := by ring_nat
        exact Nat.mul_le_mul_left 4 (e ▸ Nat.mul_le_mul hb hb)
      have h3 : 4 * (4 * (m+2) * (m+2)) ≤ wallisNum (m+1) * (4 * (m+2) * (m+2)) :=
        Nat.mul_le_mul_right _ h4
      exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)

/-- ★★★ **The Wallis pointing overtakes every schedule.**  For *any* positive
    probe schedule `ρ`, scheduled domination fails at every layer `n ≥ 2`:
    `W_n = a_n·d_n` exceeds the scheduled denominator quantum no matter how
    much polynomial slack the schedule forgives.  The Wallis pointing of π/2
    sits **beyond every rung** of the graded ladder — its rung is `∞`. -/
theorem wallis_overtakes_every_schedule (ρ : Nat → Nat) (hρ : ∀ n, 1 ≤ ρ n)
    (n : Nat) (hn : 2 ≤ n) :
    ¬ DominatesS (fun j => wallisNum j * wallisDen j) wallisDen ρ n := by
  intro hdom
  have hQ : (2*n+1) * (2*n+3) < wallisNum n := quad_lt_wallisNum n hn
  have eR : ρ (n+1) * wallisDen (n+1)
      = (ρ (n+1) * wallisDen n) * ((2*n+1) * (2*n+3)) := by
    show ρ (n+1) * (wallisDen n * ((2*n+1) * (2*n+3)))
        = (ρ (n+1) * wallisDen n) * ((2*n+1) * (2*n+3))
    ring_nat
  have hlt : (ρ (n+1) * wallisDen n) * ((2*n+1) * (2*n+3))
      < (ρ (n+1) * wallisDen n) * wallisNum n :=
    nat_mul_lt_mul_left (Nat.mul_pos (hρ (n+1)) (wallisDen_pos n)) hQ
  have hle : (ρ (n+1) * wallisDen n) * wallisNum n
      ≤ ρ n * ρ (n+1) * (wallisNum n * wallisDen n) := by
    have e1 : (ρ (n+1) * wallisDen n) * wallisNum n
        = 1 * (ρ (n+1) * (wallisNum n * wallisDen n)) := by ring_nat
    have e2 : ρ n * ρ (n+1) * (wallisNum n * wallisDen n)
        = ρ n * (ρ (n+1) * (wallisNum n * wallisDen n)) := by ring_nat
    rw [e1, e2]
    exact Nat.mul_le_mul_right _ (hρ n)
  have habs : ρ (n+1) * wallisDen (n+1) < ρ (n+1) * wallisDen (n+1) :=
    calc ρ (n+1) * wallisDen (n+1)
        = (ρ (n+1) * wallisDen n) * ((2*n+1) * (2*n+3)) := eR
      _ < (ρ (n+1) * wallisDen n) * wallisNum n := hlt
      _ ≤ ρ n * ρ (n+1) * (wallisNum n * wallisDen n) := hle
      _ ≤ ρ n * ρ (n+1) * (wallisNum n * wallisDen n) + ρ n * wallisDen n :=
          Nat.le_add_right _ _
      _ ≤ ρ (n+1) * wallisDen (n+1) := hdom
  exact Nat.lt_irrefl _ habs

/-- ★★★ **No graded rate certificate at any schedule** — the rung of the Wallis
    pointing is `∞`: for every positive schedule `ρ`, `HtelS wallisNum wallisDen ρ`
    fails (it would force scheduled domination at layer 2, which
    `wallis_overtakes_every_schedule` refutes).  Together with the conditional
    modulus (§3) this completes π's placement: the *pointing* has no finite
    rung, and what remains attributable to π itself is exactly the measure
    hypothesis `PiHalfMeasure` — the rung is a property of the pointing, not of
    the real (`PresentationDependence`; depth is intensional,
    `SpiralLayer.depth_is_intensional`). -/
theorem wallis_no_graded_certificate (ρ : Nat → Nat) (hρ : ∀ n, 1 ≤ ρ n) :
    ¬ HtelS wallisNum wallisDen ρ := fun h =>
  wallis_overtakes_every_schedule ρ hρ 2 (Nat.le_refl 2)
    (((htelS_iff_dominatesS (fun j => wallisNum j * wallisDen j)
        (fun i => wallis_cross_det i)).mp h) 2 (by decide))

end E213.Lib.Math.NumberSystems.Real213.ExpLog.PiMeasureModulus
