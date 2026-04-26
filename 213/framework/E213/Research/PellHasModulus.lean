import E213.Research.HasModulus
import E213.Research.PellSeq
import E213.Research.Sqrt2Irrational

/-!
# Research.PellHasModulus: Pell sequence 의 HasModulus instance

PAPER1 §6.4 의 LEM-bound closure 가 Pell sequence 위 에서
*완전 close*: explicit modulus N(m, k) 가 sqrt2_irrational
+ pellRaw_cut_above/below 의 합 으 로 구성.

## 핵심

`pellRawSeq : Nat → Raw := λ n. (pellRaw n).val` 의 modulus:
- `2k² < m²`: N(m, k) = k (pellRaw_cut_above 의 N).
- `m² < 2k²`: N(m, k) = 0 (pellRaw_cut_below 가 모든 n).
- `m² = 2k²`: 불가능 (sqrt2_irrational, k ≥ 1).

## 의의

Pell sequence 의 all-(m, k) Cauchy property 가 LEM 없 이
constructive 로 close.  `HasModulus xs → isOrderCauchy xs`
infrastructure 의 첫 concrete instance.
-/

namespace E213.Research.PellHasModulus

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS
open E213.Research.PellSeq
open E213.Research.Sqrt2Irrational

/-- Pell sequence as `Nat → Raw`. -/
def pellRawSeq : Nat → Raw := fun n => (pellRaw n).val

/-- Modulus 함수: above case 면 k, 아니 면 0. -/
def pellModulusN (m k : Nat) : Nat :=
  if 2 * k * k < m * m then k else 0

end E213.Research.PellHasModulus

namespace E213.Research.PellHasModulus

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS
open E213.Research.PellSeq
open E213.Research.Sqrt2Cut
open E213.Research.Sqrt2Irrational

/-- Cauchy stability at (m, k) — 3-case 분석. -/
theorem pell_cauchy_at (m k : Nat) (hk : k ≥ 1)
    (i j : Nat) (hi : i ≥ pellModulusN m k) (hj : j ≥ pellModulusN m k) :
    orderProj m k (abLens.view (pellRawSeq i)) =
    orderProj m k (abLens.view (pellRawSeq j)) := by
  unfold pellRawSeq
  by_cases h : 2 * k * k < m * m
  · -- above: both true.  Inline pellRaw_cut_above 의 logic (N = k).
    have hN : pellModulusN m k = k := if_pos h
    rw [hN] at hi hj
    have above : ∀ n, n ≥ k →
        orderProj m k (abLens.view (pellRaw n).val) = true := by
      intro n hn
      rw [pellRaw_view]
      have hyn : pellY n ≥ k := by
        have := pellY_lb n
        omega
      have hyn_sq : k * k ≤ pellY n * pellY n := Nat.mul_le_mul hyn hyn
      exact pell_orderProj_above (pellX n) (pellY n) m k
        (pell_invariant n) h hyn_sq
    rw [above i hi, above j hj]
  · -- ¬ (2k² < m²) → m² ≤ 2k².  m² = 2k² 는 불가 (sqrt2_irrational).
    have hle : m * m ≤ 2 * k * k := by omega
    have hne : m * m ≠ 2 * k * k := by
      have := sqrt2_irrational k hk m
      have h2 : 2 * (k * k) = 2 * k * k := by
        rw [Nat.mul_assoc]
      omega
    have hbelow : m * m < 2 * k * k := Nat.lt_of_le_of_ne hle hne
    rw [pellRaw_cut_below m k hk hbelow i,
        pellRaw_cut_below m k hk hbelow j]

end E213.Research.PellHasModulus

namespace E213.Research.PellHasModulus

open E213.Firmware E213.Hypervisor
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS
open E213.Research.PellSeq

/-- **Pell HasModulus instance**: explicit modulus 가 sqrt2_irrational
    + pellRaw_cut_above/below 의 합 으 로 구성.  PAPER1 §6.4
    의 LEM-bound closure 가 Pell 위 에서 LEM 없 이 close. -/
def pellHasModulus : HasModulus pellRawSeq where
  N := pellModulusN
  cauchy_at := pell_cauchy_at

/-- 따라서 Pell sequence 가 isOrderCauchy (LEM 없 이). -/
theorem pell_isOrderCauchy : isOrderCauchy pellRawSeq :=
  isOrderCauchy_of_hasModulus pellRawSeq pellHasModulus

end E213.Research.PellHasModulus
