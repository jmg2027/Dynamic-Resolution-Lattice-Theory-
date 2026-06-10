import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
import E213.Lib.Math.NumberSystems.Real213.AbCutSeq
import E213.Lib.Math.Analysis.Cauchy.PellSeq
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# CothSeriesCut — the coth series as a fold, and the two pointings meet (weld 3b)

The weld's two sides are now both *folds*:

  * the **CF pointing** `cothUnitCFCauchySeq q` (`ContinuedFractionModulus` §6) —
    unconditionally completed, modulus `k+2`;
  * the **series pointing** built here: the truncated ratio
    `T_J = (2J+1)·q·coshNum_J / sinhNum_J` (= `cosh(1/q)/sinh(1/q)` with both series
    truncated at `J`, cleared — the `(2J+1)` is the denominator-ratio `(2J+1)!/(2J)!`)
    climbs (`t_mono`, from the cross identity `tcross_id` whose `q²`-terms cancel
    exactly), so `cothSeriesAb q : AbCutSeq` is a genuine fold.

**The two pointings provably agree on concrete probes** (`two_pointings_agree`):
at `q = 1` both read `true` at `3/2` (`coth 1 ≤ 3/2` — the series side via the
uniform bound `2(2J+1)·coshNum + 1 ≤ 3·sinhNum`, an induction whose margin is
`X_{J+1} = (2J+2)(2J+3)X_J − (4J+3)`, safe from `X_0 = 1`) and `false` at `5/4`
(`coth 1 > 5/4`, layer-2 witness + nesting).  The ∀-probe agreement — the full weld —
is stage 3c: the order transfer through the §5 weld rows + §7 bridge (recorded).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut

open E213.Theory (Raw)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.Analysis.Cauchy.Archimedean (orderProj)
open E213.Lib.Math.Analysis.Cauchy.PellSeq (abLens_witness)
open E213.Lib.Math.Analysis.Cauchy.MonotonicBounded (IsAbMonotonic IsAbPositiveB)
open E213.Lib.Math.NumberSystems.Real213 (AbCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld (coshNum sinhNum)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
  (cothCF cothUnitCFCauchySeq)

private theorem le_of_add_le_add_right' {a b k : Nat} (h : a + k ≤ b + k) : a ≤ b :=
  E213.Tactic.NatHelper.le_of_add_le_add_left (a := k) (by
    rw [Nat.add_comm k a, Nat.add_comm k b]; exact h)

/-! ## §1 — positivity and the cosh ≤ sinh comparison -/

theorem coshNum_pos (q : Nat) : ∀ J, 1 ≤ coshNum q J
  | 0 => Nat.le_refl 1
  | _ + 1 => Nat.le_add_left 1 _

theorem sinhNum_pos (q : Nat) : ∀ J, 1 ≤ sinhNum q J
  | 0 => Nat.le_refl 1
  | _ + 1 => Nat.le_add_left 1 _

/-- Termwise `cosh ≤ sinh` (cleared): `coshNum q J ≤ sinhNum q J` — each cosh
    denominator ratio `(2J)!/(2j)!` divides the sinh one `(2J+1)!/(2j+1)!`. -/
theorem cosh_le_sinh (q : Nat) : ∀ J, coshNum q J ≤ sinhNum q J
  | 0 => Nat.le_refl 1
  | J + 1 => by
    show (2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1
        ≤ (2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1
    refine Nat.add_le_add_right ?_ 1
    exact Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.le_succ (2 * J + 1)) (Nat.le_succ (2 * J + 2)))
        (Nat.le_refl (q ^ 2)))
      (cosh_le_sinh q J)

/-! ## §2 — the truncated coth ratio climbs -/

/-- The cross identity behind monotonicity: the `q²`-terms of
    `(2J+3)·cosh_{J+1}·sinh_J − (2J+1)·cosh_J·sinh_{J+1}` cancel **exactly**, leaving
    `(2J+3)·sinh_J − (2J+1)·cosh_J` (stated additively). -/
theorem tcross_id (q J : Nat) :
    (2 * J + 1) * coshNum q J * sinhNum q (J + 1) + (2 * J + 3) * sinhNum q J
      = (2 * J + 3) * coshNum q (J + 1) * sinhNum q J + (2 * J + 1) * coshNum q J := by
  show (2 * J + 1) * coshNum q J
        * ((2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1)
        + (2 * J + 3) * sinhNum q J
      = (2 * J + 3) * ((2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1)
        * sinhNum q J + (2 * J + 1) * coshNum q J
  ring_nat

/-- ★★★ **The truncated coth ratio climbs**:
    `(2J+1)·cosh_J·sinh_{J+1} ≤ (2J+3)·cosh_{J+1}·sinh_J` — from the cross identity
    and `(2J+1)·cosh ≤ (2J+3)·sinh`. -/
theorem t_mono (q J : Nat) :
    (2 * J + 1) * coshNum q J * sinhNum q (J + 1)
      ≤ (2 * J + 3) * coshNum q (J + 1) * sinhNum q J := by
  have hle : (2 * J + 1) * coshNum q J ≤ (2 * J + 3) * sinhNum q J :=
    Nat.mul_le_mul
      (Nat.le_trans (Nat.le_succ (2 * J + 1)) (Nat.le_succ (2 * J + 2)))
      (cosh_le_sinh q J)
  have h3 : (2 * J + 1) * coshNum q J * sinhNum q (J + 1) + (2 * J + 1) * coshNum q J
      ≤ (2 * J + 3) * coshNum q (J + 1) * sinhNum q J + (2 * J + 1) * coshNum q J := by
    calc (2 * J + 1) * coshNum q J * sinhNum q (J + 1) + (2 * J + 1) * coshNum q J
        ≤ (2 * J + 1) * coshNum q J * sinhNum q (J + 1) + (2 * J + 3) * sinhNum q J :=
          Nat.add_le_add_left hle _
      _ = (2 * J + 3) * coshNum q (J + 1) * sinhNum q J + (2 * J + 1) * coshNum q J :=
          tcross_id q J
  exact le_of_add_le_add_right' h3

/-! ## §3 — the series fold -/

/-- Numerator of the truncated coth: `T_J = (2J+1)·q·coshNum_J / sinhNum_J`. -/
def TNum (q J : Nat) : Nat := (2 * J + 1) * q * coshNum q J

theorem TNum_pos (q : Nat) (hq : 1 ≤ q) (J : Nat) : 1 ≤ TNum q J :=
  Nat.le_trans
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_add_left 1 (2 * J)) hq) (coshNum_pos q J))
    (Nat.le_refl _)

/-- The coth-truncation Raw at layer `J`: `(TNum q J, sinhNum q J)`. -/
def cothSeriesRaw (q : Nat) (hq : 1 ≤ q) (J : Nat) :
    {r : Raw // abLens.view r = (TNum q J, sinhNum q J)} :=
  abLens_witness (TNum q J + sinhNum q J) (TNum q J) (sinhNum q J) rfl
    (TNum_pos q hq J) (sinhNum_pos q J)

def cothSeriesRawSeq (q : Nat) (hq : 1 ≤ q) : Nat → Raw :=
  fun J => (cothSeriesRaw q hq J).val

theorem cothSeries_isAbMonotonic (q : Nat) (hq : 1 ≤ q) :
    IsAbMonotonic (cothSeriesRawSeq q hq) := by
  intro J
  show (abLens.view (cothSeriesRaw q hq J).val).1
        * (abLens.view (cothSeriesRaw q hq (J + 1)).val).2
      ≤ (abLens.view (cothSeriesRaw q hq (J + 1)).val).1
        * (abLens.view (cothSeriesRaw q hq J).val).2
  rw [(cothSeriesRaw q hq J).property, (cothSeriesRaw q hq (J + 1)).property]
  show TNum q J * sinhNum q (J + 1) ≤ TNum q (J + 1) * sinhNum q J
  have h := Nat.mul_le_mul (Nat.le_refl q) (t_mono q J)
  calc TNum q J * sinhNum q (J + 1)
      = q * ((2 * J + 1) * coshNum q J * sinhNum q (J + 1)) := by
        show (2 * J + 1) * q * coshNum q J * sinhNum q (J + 1) = _
        ring_nat
    _ ≤ q * ((2 * J + 3) * coshNum q (J + 1) * sinhNum q J) := h
    _ = TNum q (J + 1) * sinhNum q J := by
        show _ = (2 * (J + 1) + 1) * q * coshNum q (J + 1) * sinhNum q J
        ring_nat

theorem cothSeries_isAbPositiveB (q : Nat) (hq : 1 ≤ q) :
    IsAbPositiveB (cothSeriesRawSeq q hq) := by
  intro J
  show 1 ≤ (abLens.view (cothSeriesRaw q hq J).val).2
  rw [(cothSeriesRaw q hq J).property]
  exact sinhNum_pos q J

/-- ★★★★ **The coth series pointing as a fold**: the truncated ratios
    `(2J+1)·q·coshNum_J / sinhNum_J` climb, so the series side of the weld is an
    `AbCutSeq` — the cut interface (layer `ValidCut`s, nesting, eventual constancy,
    completion-given-modulus) is generic.  The weld (stage 3c) will identify its sup
    with the CF fold's. -/
def cothSeriesAb (q : Nat) (hq : 1 ≤ q) : AbCutSeq :=
  ⟨cothSeriesRawSeq q hq, cothSeries_isAbMonotonic q hq, cothSeries_isAbPositiveB q hq⟩

/-- The layer cut, `constCut`-viewed. -/
theorem cothSeriesCut_eq (q : Nat) (hq : 1 ≤ q) (n m k : Nat) :
    (cothSeriesAb q hq).cut n m k = decide (TNum q n * k ≤ sinhNum q n * m) := by
  show orderProj m k (abLens.view (cothSeriesRaw q hq n).val) = _
  rw [(cothSeriesRaw q hq n).property]; rfl

/-! ## §4 — the two pointings agree on concrete probes (`q = 1`) -/

/-- The uniform `3/2`-bound for the `q = 1` series: `2(2J+1)·coshNum + 1 ≤ 3·sinhNum`
    at every truncation (`coth 1 < 3/2` with margin ≥ 1; the margin recursion is
    `X_{J+1} = (2J+2)(2J+3)·X_J − (4J+3)`, safe from `X_0 = 1`). -/
theorem coth1_le_three_halves : ∀ J, 2 * (2 * J + 1) * coshNum 1 J + 1 ≤ 3 * sinhNum 1 J
  | 0 => by decide
  | J + 1 => by
    have ih := coth1_le_three_halves J
    have hc : coshNum 1 (J + 1) = (2 * J + 1) * (2 * J + 2) * coshNum 1 J + 1 := by
      show (2 * J + 1) * (2 * J + 2) * 1 ^ 2 * coshNum 1 J + 1 = _
      rw [show ((1 : Nat) ^ 2) = 1 from rfl, Nat.mul_one]
    have hs : sinhNum 1 (J + 1) = (2 * J + 2) * (2 * J + 3) * sinhNum 1 J + 1 := by
      show (2 * J + 2) * (2 * J + 3) * 1 ^ 2 * sinhNum 1 J + 1 = _
      rw [show ((1 : Nat) ^ 2) = 1 from rfl, Nat.mul_one]
    show 2 * (2 * (J + 1) + 1) * coshNum 1 (J + 1) + 1 ≤ 3 * sinhNum 1 (J + 1)
    rw [hc, hs]
    apply le_of_add_le_add_right' (k := (2 * J + 2) * (2 * J + 3))
    calc 2 * (2 * (J + 1) + 1) * ((2 * J + 1) * (2 * J + 2) * coshNum 1 J + 1) + 1
          + (2 * J + 2) * (2 * J + 3)
        = (2 * J + 2) * (2 * J + 3) * (2 * (2 * J + 1) * coshNum 1 J + 1)
          + (4 * J + 7) := by ring_nat
      _ ≤ (2 * J + 2) * (2 * J + 3) * (3 * sinhNum 1 J) + (4 * J + 7) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ ≤ (2 * J + 2) * (2 * J + 3) * (3 * sinhNum 1 J)
          + ((2 * J + 2) * (2 * J + 3) + 3) :=
          Nat.add_le_add_left
            (Nat.le.intro (show 4 * J + 7 + (4 * J * J + 6 * J + 2)
                = (2 * J + 2) * (2 * J + 3) + 3 from by ring_nat)) _
      _ = 3 * ((2 * J + 2) * (2 * J + 3) * sinhNum 1 J + 1)
          + (2 * J + 2) * (2 * J + 3) := by ring_nat

/-- The series cut reads `true` at `3/2` at **every** layer (`coth 1 ≤ 3/2`). -/
theorem coth1_series_at_3_2 (n : Nat) :
    (cothSeriesAb 1 (Nat.le_refl 1)).cut n 3 2 = true := by
  rw [cothSeriesCut_eq]
  apply decide_eq_true
  show (2 * n + 1) * 1 * coshNum 1 n * 2 ≤ sinhNum 1 n * 3
  have h := Nat.le_of_succ_le (coth1_le_three_halves n)
  calc (2 * n + 1) * 1 * coshNum 1 n * 2
      = 2 * (2 * n + 1) * coshNum 1 n := by ring_nat
    _ ≤ 3 * sinhNum 1 n := h
    _ = sinhNum 1 n * 3 := Nat.mul_comm 3 _

/-- The series cut reads `false` at `5/4` from layer 2 on (`coth 1 > 5/4`):
    layer-2 witness `185·4 > 141·5` + generic nesting. -/
theorem coth1_series_at_5_4 (n : Nat) (hn : 2 ≤ n) :
    (cothSeriesAb 1 (Nat.le_refl 1)).cut n 5 4 = false := by
  have h2 : (cothSeriesAb 1 (Nat.le_refl 1)).cut 2 5 4 = false := by
    rw [cothSeriesCut_eq]; decide
  exact (cothSeriesAb 1 (Nat.le_refl 1)).cut_false_fwd 5 4 2 h2 n hn

/-- ★★★★★ **The two pointings of `coth 1` agree on the bracket probes**: the CF fold's
    completed limit and the series fold's layer cuts both read `true` at `3/2` and
    `false` at `5/4` — the Lambert real and the coth series are pinned in the same
    bracket `(5/4, 3/2]`, by two entirely different pointings (CF: unconditional
    modulus `k+2`; series: the uniform `3/2`-bound + a layer-2 witness).  The
    ∀-probe agreement is stage 3c (the order transfer through the weld rows and the
    evaluation bridge). -/
theorem two_pointings_agree :
    ((cothUnitCFCauchySeq 1 (Nat.le_refl 1)).limit 3 2 = true
      ∧ ∀ n, (cothSeriesAb 1 (Nat.le_refl 1)).cut n 3 2 = true)
    ∧ ((cothUnitCFCauchySeq 1 (Nat.le_refl 1)).limit 5 4 = false
      ∧ ∀ n, 2 ≤ n → (cothSeriesAb 1 (Nat.le_refl 1)).cut n 5 4 = false) :=
  ⟨⟨by decide, coth1_series_at_3_2⟩, ⟨by decide, coth1_series_at_5_4⟩⟩

/-! ## §5 — the upper transfer, first instance: `T_J` below the first odd convergent

The order transfer's upper half says `T_J ≤` every odd CF convergent.  Its first
instance is provable now by the same margin induction as the `3/2`-bound: at `q = 1`
the first odd convergent is `cfPn 1/cfQn 1 = 4/3`, and `T_J < 4/3` uniformly — the
margin `X_J = 4·sinhNum − 3(2J+1)·coshNum` obeys `X_{J+1} = (2J+2)(2J+3)X_J − (6J+5)`,
safe from `X_0 = 1`.  (The ∀-convergent version is stage 3c, through `row_det`.) -/

/-- `T_J < 4/3` uniformly (`q = 1`): `3(2J+1)·coshNum + 1 ≤ 4·sinhNum`. -/
theorem coth1_lt_4_3 : ∀ J, 3 * (2 * J + 1) * coshNum 1 J + 1 ≤ 4 * sinhNum 1 J
  | 0 => by decide
  | J + 1 => by
    have ih := coth1_lt_4_3 J
    have hc : coshNum 1 (J + 1) = (2 * J + 1) * (2 * J + 2) * coshNum 1 J + 1 := by
      show (2 * J + 1) * (2 * J + 2) * 1 ^ 2 * coshNum 1 J + 1 = _
      rw [show ((1 : Nat) ^ 2) = 1 from rfl, Nat.mul_one]
    have hs : sinhNum 1 (J + 1) = (2 * J + 2) * (2 * J + 3) * sinhNum 1 J + 1 := by
      show (2 * J + 2) * (2 * J + 3) * 1 ^ 2 * sinhNum 1 J + 1 = _
      rw [show ((1 : Nat) ^ 2) = 1 from rfl, Nat.mul_one]
    show 3 * (2 * (J + 1) + 1) * coshNum 1 (J + 1) + 1 ≤ 4 * sinhNum 1 (J + 1)
    rw [hc, hs]
    apply le_of_add_le_add_right' (k := (2 * J + 2) * (2 * J + 3))
    calc 3 * (2 * (J + 1) + 1) * ((2 * J + 1) * (2 * J + 2) * coshNum 1 J + 1) + 1
          + (2 * J + 2) * (2 * J + 3)
        = (2 * J + 2) * (2 * J + 3) * (3 * (2 * J + 1) * coshNum 1 J + 1)
          + (6 * J + 10) := by ring_nat
      _ ≤ (2 * J + 2) * (2 * J + 3) * (4 * sinhNum 1 J) + (6 * J + 10) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ ≤ (2 * J + 2) * (2 * J + 3) * (4 * sinhNum 1 J)
          + ((2 * J + 2) * (2 * J + 3) + 4) :=
          Nat.add_le_add_left
            (Nat.le.intro (show 6 * J + 10 + (4 * J * J + 4 * J)
                = (2 * J + 2) * (2 * J + 3) + 4 from by ring_nat)) _
      _ = 4 * ((2 * J + 2) * (2 * J + 3) * sinhNum 1 J + 1)
          + (2 * J + 2) * (2 * J + 3) := by ring_nat

/-- ★★★ **The series fold sits below the first odd CF convergent, uniformly**: the
    series cut reads `true` at `4/3 = cfPn 1/cfQn 1` at every layer — the first
    instance of the upper order transfer (`T_J ≤ r₁`), by the margin induction.  The
    ∀-convergent upper transfer is stage 3c. -/
theorem coth1_series_below_first_odd (n : Nat) :
    (cothSeriesAb 1 (Nat.le_refl 1)).cut n 4 3 = true := by
  rw [cothSeriesCut_eq]
  apply decide_eq_true
  show (2 * n + 1) * 1 * coshNum 1 n * 3 ≤ sinhNum 1 n * 4
  have h := Nat.le_of_succ_le (coth1_lt_4_3 n)
  calc (2 * n + 1) * 1 * coshNum 1 n * 3
      = 3 * (2 * n + 1) * coshNum 1 n := by ring_nat
    _ ≤ 4 * sinhNum 1 n := h
    _ = sinhNum 1 n * 4 := Nat.mul_comm 4 _

end E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut
