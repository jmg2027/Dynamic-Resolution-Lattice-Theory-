import E213.Research.Modulus.HasModulus
import E213.Research.Cauchy.PellSeq
import E213.Research.Irrational.Sqrt2KernelFree

/-!
# Research.PellHasModulus: HasModulus instance for the Pell sequence

The LEM-bound closure of PAPER1 §6.4 *fully closes* on the Pell
sequence: the explicit modulus N(m, k) is constructed from the
combination of sqrt2_irrational and pellRaw_cut_above/below.

## Core

Modulus for `pellRawSeq : Nat → Raw := λ n. (pellRaw n).val`:
- `2k² < m²`: N(m, k) = k (the N of pellRaw_cut_above).
- `m² < 2k²`: N(m, k) = 0 (pellRaw_cut_below holds for all n).
- `m² = 2k²`: impossible (sqrt2_irrational, k ≥ 1).

## Significance

The all-(m, k) Cauchy property of the Pell sequence closes
constructively without LEM.  The first concrete instance of the
`HasModulus xs → isOrderCauchy xs` infrastructure.
-/

namespace E213.Research.PellHasModulus

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS
open E213.Research.PellSeq
open E213.Research.Sqrt2IrrationalKernelFree

/-- Pell sequence as `Nat → Raw`. -/
def pellRawSeq : Nat → Raw := fun n => (pellRaw n).val

/-- Modulus function: k in the above case, 0 otherwise. -/
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
open E213.Research.Sqrt2IrrationalKernelFree

/-- Cauchy stability at (m, k) — 3-case analysis. -/
theorem pell_cauchy_at (m k : Nat) (hk : k ≥ 1)
    (i j : Nat) (hi : i ≥ pellModulusN m k) (hj : j ≥ pellModulusN m k) :
    orderProj m k (abLens.view (pellRawSeq i)) =
    orderProj m k (abLens.view (pellRawSeq j)) := by
  unfold pellRawSeq
  by_cases h : 2 * k * k < m * m
  · -- above: both true.  Inline the logic of pellRaw_cut_above (N = k).
    have hN : pellModulusN m k = k := if_pos h
    rw [hN] at hi hj
    have above : ∀ n, n ≥ k →
        orderProj m k (abLens.view (pellRaw n).val) = true := by
      intro n hn
      rw [pellRaw_view]
      have hyn : pellY n ≥ k := by
        have hlb := pellY_lb n  -- pellY n ≥ n + 2
        have h1 : k ≤ k + 2 := Nat.le_add_right k 2
        have h2 : k + 2 ≤ n + 2 := Nat.add_le_add_right hn 2
        exact Nat.le_trans (Nat.le_trans h1 h2) hlb
      have hyn_sq : k * k ≤ pellY n * pellY n := Nat.mul_le_mul hyn hyn
      exact pell_orderProj_above (pellX n) (pellY n) m k
        (pell_invariant n) h hyn_sq
    rw [above i hi, above j hj]
  · -- ¬ (2k² < m²) → m² ≤ 2k².  m² = 2k² is impossible (sqrt2_irrational).
    have hle : m * m ≤ 2 * k * k := Nat.le_of_not_lt h
    have hne : m * m ≠ 2 * k * k := by
      intro heq
      have h2 : 2 * (k * k) = 2 * k * k := by rw [Nat.mul_assoc]
      exact sqrt2_irrational k hk m (heq.trans h2.symm)
    have hbelow : m * m < 2 * k * k := Nat.lt_of_le_of_ne hle hne
    rw [pellRaw_cut_below m k hk hbelow i,
        pellRaw_cut_below m k hk hbelow j]

end E213.Research.PellHasModulus

namespace E213.Research.PellHasModulus

open E213.Firmware E213.Hypervisor
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS
open E213.Research.PellSeq

/-- **Pell HasModulus instance**: the explicit modulus is constructed
    from the combination of sqrt2_irrational and
    pellRaw_cut_above/below.  The LEM-bound closure of PAPER1 §6.4
    closes on Pell without LEM. -/
def pellHasModulus : HasModulus pellRawSeq where
  N := pellModulusN
  cauchy_at := pell_cauchy_at

/-- Therefore the Pell sequence is isOrderCauchy (without LEM). -/
theorem pell_isOrderCauchy : isOrderCauchy pellRawSeq :=
  isOrderCauchy_of_hasModulus pellRawSeq pellHasModulus

end E213.Research.PellHasModulus
