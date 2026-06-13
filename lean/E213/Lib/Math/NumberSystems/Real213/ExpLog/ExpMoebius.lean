import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuedFractionModulus
import E213.Meta.Nat.NatRing213
import E213.Meta.Nat.PolyNatMTactic

/-!
# ExpMoebius — `exp(2/q)` completes unconditionally (the cut-Möbius step)

`ExpUnitModulus.exp_pq_no_htel` proved the factorial presentation of `exp(p/q)`
(`p ≥ 2`) carries **no** rate certificate; `ExpRationalCut` isolated the missing
modulus in one measure hypothesis.  This file *discharges the goal* by switching
presentations: `e^{2/q} = (coth(1/q) + 1)/(coth(1/q) − 1)`, and the Möbius map
`z ↦ (z+1)/(z−1)` carries the Lambert fold's **odd** convergents (descending onto
`coth(1/q)`) to a **climbing** sequence

  `x_L = (p_{2L+1} + q_{2L+1}) / (p_{2L+1} − q_{2L+1})  ↗  e^{2/q}`,

whose cross-determinant is **exactly twice the partial quotient**:
`x`-cross `= 2·(p_{2L+1}q_{2L+3} − p_{2L+3}q_{2L+1}) = 2·a_{2L+3}` — the same
det-one-floor amplification that completes every explicit continued fraction
(`cf_universal_total_modulus`), so the whole rate machinery applies verbatim:

  * the denominators `dₙ = pₙ − qₙ` obey the **same three-term recurrence**
    (`dN`, subtraction-free; `qₙ + dₙ = pₙ` is the invariant `dN_add`), grow
    Fibonacci-fast (`dN_ge_self`), and the smallness condition closes;
  * ★ `expTwoOverQCFCauchySeq` — **`exp(2/q)` as a genuine `CauchyCutSeq`, total
    modulus `N(m,k) = k + 2`, no hypotheses beyond `q ≥ 1`** — no measure, no
    rate assumption, no LEM;
  * anchors: `e² ∈ (22/3, 37/5]` — the CF pointing localizes `e²` in
    `(7.3̄, 7.4]`, sharper than the series bracket `(7, 904/120]` of
    `ExpRationalCut`.

The presentation-dependence is the content: the *series* pointing of `exp(2/q)`
provably carries no modulus, the *Möbius-of-CF* pointing carries a universal one
— rate is a property of the pointing, not the real.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpMoebius

open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
  (cfPn cfPn_pos cfP_eq_cast cothCF cothCF_pos mono_of_step)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor
  (cfP cfQ cfQn cfQn_pos cfQ_eq_cast cfDet cfDet2 cfDet2_eq cf_det_even cf_det_step)
open E213.Lib.Math.NumberSystems.Real213.RateModulus
  (rcut rate_cut_const Htel_of_crossdet)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Meta.Nat.NatRing213 (nat_add_right_cancel)

/-! ## §1 — the difference sequence `dₙ = pₙ − qₙ`, subtraction-free -/

/-- `dₙ = pₙ − qₙ` of the Lambert fold, by the convergent recurrence itself
    (the difference of two solutions is a solution): `d₀ = q − 1`,
    `d₁ = 3q(q−1) + 1`, `d_{n+2} = a_{n+2}d_{n+1} + dₙ`. -/
def dN (q : Nat) : Nat → Nat
  | 0 => q - 1
  | 1 => 3 * q * (q - 1) + 1
  | n + 2 => cothCF q (n + 2) * dN q (n + 1) + dN q n

private theorem one_add_pred {q : Nat} (hq : 1 ≤ q) : 1 + (q - 1) = q := by
  cases q with
  | zero => exact absurd hq (Nat.not_succ_le_zero 0)
  | succ e => exact Nat.add_comm 1 e

/-- The invariant `qₙ + dₙ = pₙ` (`coth(1/q) > 1`: numerators exceed
    denominators, with `dN` the exact excess). -/
theorem dN_add (q : Nat) (hq : 1 ≤ q) : ∀ n,
    cfQn (cothCF q) n + dN q n = cfPn (cothCF q) n
  | 0 => by
    show 1 + (q - 1) = 1 * q
    rw [Nat.one_mul]
    exact one_add_pred hq
  | 1 => by
    show 3 * q + (3 * q * (q - 1) + 1) = 3 * q * (1 * q) + 1
    rw [Nat.one_mul]
    calc 3 * q + (3 * q * (q - 1) + 1)
        = 3 * q * (q - 1) + 3 * q * 1 + 1 := by ring_nat
      _ = 3 * q * ((q - 1) + 1) + 1 := by ring_nat
      _ = 3 * q * q + 1 := by
          rw [show (q - 1) + 1 = q from by rw [Nat.add_comm]; exact one_add_pred hq]
  | n + 2 => by
    show cothCF q (n + 2) * cfQn (cothCF q) (n + 1) + cfQn (cothCF q) n
          + (cothCF q (n + 2) * dN q (n + 1) + dN q n)
        = cothCF q (n + 2) * cfPn (cothCF q) (n + 1) + cfPn (cothCF q) n
    rw [← dN_add q hq (n + 1), ← dN_add q hq n]
    ring_nat

theorem dN_pos (q : Nat) (hq : 1 ≤ q) : ∀ n, 1 ≤ dN q (n + 1)
  | 0 => Nat.le_add_left 1 _
  | n + 1 => by
    show 1 ≤ cothCF q (n + 2) * dN q (n + 1) + dN q n
    exact Nat.le_trans
      (Nat.le_trans (dN_pos q hq n)
        (Nat.le_mul_of_pos_left (dN q (n + 1)) (cothCF_pos q hq (n + 2))))
      (Nat.le_add_right _ _)

/-- Fibonacci-floor growth of the excess: `n ≤ d_{n+1}` (the partial quotients
    `≥ 3` make the excess outgrow the index). -/
theorem dN_ge_self (q : Nat) (hq : 1 ≤ q) : ∀ n, n ≤ dN q (n + 1)
  | 0 => Nat.zero_le _
  | 1 => dN_pos q hq 1
  | n + 2 => by
    have ih := dN_ge_self q hq (n + 1)
    have ha3 : 3 ≤ cothCF q (n + 3) := by
      show 3 ≤ (2 * (n + 3) + 1) * q
      calc 3 = 3 * 1 := (Nat.mul_one 3).symm
        _ ≤ (2 * (n + 3) + 1) * q :=
          Nat.mul_le_mul (Nat.le_add_left 3 (2 * n + 4)) hq
    show n + 2 ≤ cothCF q (n + 3) * dN q (n + 2) + dN q (n + 1)
    calc n + 2 ≤ 3 * (n + 1) := Nat.le.intro (show n + 2 + (2 * n + 1) = 3 * (n + 1)
          from by ring_nat)
      _ ≤ 3 * dN q (n + 2) := Nat.mul_le_mul_left 3 ih
      _ ≤ cothCF q (n + 3) * dN q (n + 2) :=
          Nat.mul_le_mul_right (dN q (n + 2)) ha3
      _ ≤ cothCF q (n + 3) * dN q (n + 2) + dN q (n + 1) := Nat.le_add_right _ _

/-! ## §2 — the Möbius convergents and their doubled cross-determinant -/

/-- Numerators of the `exp(2/q)` convergents: `p_{2L+1} + q_{2L+1}`. -/
def eNum (q L : Nat) : Nat :=
  cfPn (cothCF q) (2 * L + 1) + cfQn (cothCF q) (2 * L + 1)

/-- Denominators: `p_{2L+1} − q_{2L+1}` (= `dN` at the odd index). -/
def eDen (q L : Nat) : Nat := dN q (2 * L + 1)

/-- The one-step determinant at an odd index is `−1`. -/
theorem cf_det_odd (a : Nat → Nat) (n : Nat) : cfDet a (2 * n + 1) = -1 := by
  rw [cf_det_step a (2 * n), cf_det_even a n]

private theorem mul_neg_one_int (x : Int) : x * (-1) = -x := by
  cases x with
  | ofNat n => show Int.negOfNat (n * 1) = Int.negOfNat n; rw [Nat.mul_one]
  | negSucc n => show Int.ofNat (n.succ * 1) = Int.ofNat n.succ; rw [Nat.mul_one]

private theorem int_shuffle {X Y a : Int} (h : X + -Y = -a) : Y = X + a := by
  have hX : X = Y + -a := by
    have e : Y + -a = X := by
      rw [← h, ← E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm Y X,
          E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_neg_cancel, Int.add_zero]
    exact e.symm
  calc Y = Y + 0 := (Int.add_zero Y).symm
    _ = Y + (-a + a) := by
        rw [E213.Meta.Int213.add_comm (-a) a, E213.Meta.Int213.add_neg_cancel]
    _ = Y + -a + a := (E213.Meta.Int213.add_assoc Y (-a) a).symm
    _ = X + a := by rw [hX]

/-- The two-step determinant at an odd index, over `ℕ`:
    `p_{2n+1}·q_{2n+3} = p_{2n+3}·q_{2n+1} + a_{2n+3}` — the odd convergents
    descend with gap exactly the partial quotient. -/
theorem det2_odd_nat (a : Nat → Nat) (n : Nat) :
    cfPn a (2 * n + 1) * cfQn a (2 * n + 3)
      = cfPn a (2 * n + 3) * cfQn a (2 * n + 1) + a (2 * n + 3) := by
  have h : cfP a (2 * n + 3) * cfQ a (2 * n + 1)
      + -(cfP a (2 * n + 1) * cfQ a (2 * n + 3)) = -(a (2 * n + 3) : Int) := by
    have h0 : cfDet2 a (2 * n + 1) = -(a (2 * n + 3) : Int) := by
      rw [cfDet2_eq a (2 * n + 1), cf_det_odd a n, mul_neg_one_int]
    exact h0
  have h2 := int_shuffle h
  rw [cfP_eq_cast a (2 * n + 1), cfQ_eq_cast a (2 * n + 3), cfP_eq_cast a (2 * n + 3),
      cfQ_eq_cast a (2 * n + 1)] at h2
  have goal_int : (↑(cfPn a (2 * n + 1) * cfQn a (2 * n + 3)) : Int)
      = ↑(cfPn a (2 * n + 3) * cfQn a (2 * n + 1) + a (2 * n + 3)) := by
    rw [Int.ofNat_mul, Int.ofNat_add, Int.ofNat_mul]
    exact h2
  exact Int.ofNat.inj goal_int

/-- The `(q, d)`-pair two-step determinant: `q_{2L+3}·d_{2L+1} = q_{2L+1}·d_{2L+3}
    + a_{2L+3}` — substitute `p = q + d` into `det2_odd_nat` and cancel. -/
theorem qd_det (q : Nat) (hq : 1 ≤ q) (L : Nat) :
    cfQn (cothCF q) (2 * L + 3) * dN q (2 * L + 1)
      = cfQn (cothCF q) (2 * L + 1) * dN q (2 * L + 3) + cothCF q (2 * L + 3) := by
  have hp := dN_add q hq (2 * L + 1)
  have hp' := dN_add q hq (2 * L + 3)
  have hdet := det2_odd_nat (cothCF q) L
  apply nat_add_right_cancel
    (b := cfQn (cothCF q) (2 * L + 1) * cfQn (cothCF q) (2 * L + 3))
  calc cfQn (cothCF q) (2 * L + 3) * dN q (2 * L + 1)
        + cfQn (cothCF q) (2 * L + 1) * cfQn (cothCF q) (2 * L + 3)
      = (cfQn (cothCF q) (2 * L + 1) + dN q (2 * L + 1))
        * cfQn (cothCF q) (2 * L + 3) := by ring_nat
    _ = cfPn (cothCF q) (2 * L + 1) * cfQn (cothCF q) (2 * L + 3) := by rw [hp]
    _ = cfPn (cothCF q) (2 * L + 3) * cfQn (cothCF q) (2 * L + 1)
        + cothCF q (2 * L + 3) := hdet
    _ = (cfQn (cothCF q) (2 * L + 3) + dN q (2 * L + 3))
          * cfQn (cothCF q) (2 * L + 1) + cothCF q (2 * L + 3) := by rw [hp']
    _ = (cfQn (cothCF q) (2 * L + 1) * dN q (2 * L + 3) + cothCF q (2 * L + 3))
          + cfQn (cothCF q) (2 * L + 1) * cfQn (cothCF q) (2 * L + 3) := by ring_nat

/-- ★★★★ **The Möbius cross-determinant is twice the partial quotient**:
    `x_{L+1}·d_L = x_L·d_{L+1} + 2·a_{2L+3}` (cross-multiplied) — the `+1` and
    `−1` of the Möbius map double the det-one floor, and the climb is strict. -/
theorem e_hW (q : Nat) (hq : 1 ≤ q) (L : Nat) :
    eNum q (L + 1) * eDen q L = eNum q L * eDen q (L + 1) + 2 * cothCF q (2 * L + 3) := by
  have hp := dN_add q hq (2 * L + 1)
  have hp' := dN_add q hq (2 * L + 3)
  have hqd := qd_det q hq L
  show (cfPn (cothCF q) (2 * L + 3) + cfQn (cothCF q) (2 * L + 3)) * dN q (2 * L + 1)
      = (cfPn (cothCF q) (2 * L + 1) + cfQn (cothCF q) (2 * L + 1)) * dN q (2 * L + 3)
        + 2 * cothCF q (2 * L + 3)
  rw [← hp, ← hp']
  calc (cfQn (cothCF q) (2 * L + 3) + dN q (2 * L + 3) + cfQn (cothCF q) (2 * L + 3))
        * dN q (2 * L + 1)
      = (cfQn (cothCF q) (2 * L + 3) * dN q (2 * L + 1))
        + (cfQn (cothCF q) (2 * L + 3) * dN q (2 * L + 1))
        + dN q (2 * L + 3) * dN q (2 * L + 1) := by ring_nat
    _ = (cfQn (cothCF q) (2 * L + 1) * dN q (2 * L + 3) + cothCF q (2 * L + 3))
        + (cfQn (cothCF q) (2 * L + 1) * dN q (2 * L + 3) + cothCF q (2 * L + 3))
        + dN q (2 * L + 3) * dN q (2 * L + 1) := by rw [hqd]
    _ = (cfQn (cothCF q) (2 * L + 1) + dN q (2 * L + 1) + cfQn (cothCF q) (2 * L + 1))
          * dN q (2 * L + 3) + 2 * cothCF q (2 * L + 3) := by ring_nat

theorem eDen_pos (q : Nat) (hq : 1 ≤ q) (L : Nat) : 1 ≤ eDen q L :=
  dN_pos q hq (2 * L)

theorem eNum_pos (q : Nat) (hq : 1 ≤ q) (L : Nat) : 1 ≤ eNum q L :=
  Nat.le_trans (cfPn_pos (cothCF q) (cothCF_pos q hq) (2 * L + 1))
    (Nat.le_add_right _ _)

theorem e_hpos (q : Nat) (hq : 1 ≤ q) (i : Nat) : 0 < eNum q i * eDen q i :=
  Nat.mul_pos (eNum_pos q hq i) (eDen_pos q hq i)

/-- The strict climb: `x_L < x_{L+1}` (the cross gap is `2·a_{2L+3} ≥ 1`). -/
theorem e_hmonoS (q : Nat) (hq : 1 ≤ q) (i : Nat) :
    eNum q i * eDen q (i + 1) < eNum q (i + 1) * eDen q i := by
  rw [e_hW q hq i]
  exact Nat.lt_add_of_pos_right
    (Nat.lt_of_lt_of_le (Nat.zero_lt_one)
      (Nat.le_trans (cothCF_pos q hq (2 * i + 3))
        (Nat.le_mul_of_pos_left (cothCF q (2 * i + 3)) (by decide))))

theorem e_hmono (q : Nat) (hq : 1 ≤ q) :
    ∀ N i, N ≤ i → eNum q N * eDen q i ≤ eNum q i * eDen q N :=
  mono_of_step (e_hpos q hq) (fun n => Nat.le_of_lt (e_hmonoS q hq n))

/-- The smallness condition: the doubled partial quotient is dominated by the
    Fibonacci-fast excess (`2i ≤ d_{2i+2}` via `dN_ge_self`). -/
theorem e_hcs (q : Nat) (hq : 1 ≤ q) (i : Nat) (_ : 1 ≤ i) :
    i * (i + 1) * (2 * cothCF q (2 * i + 3)) + i * eDen q i
      ≤ (i + 1) * eDen q (i + 1) := by
  have hd2 : 2 * i ≤ dN q (2 * i + 2) :=
    Nat.le_trans (Nat.le_succ (2 * i)) (dN_ge_self q hq (2 * i + 1))
  show i * (i + 1) * (2 * cothCF q (2 * i + 3)) + i * dN q (2 * i + 1)
      ≤ (i + 1) * (cothCF q (2 * i + 3) * dN q (2 * i + 2) + dN q (2 * i + 1))
  calc i * (i + 1) * (2 * cothCF q (2 * i + 3)) + i * dN q (2 * i + 1)
      = (i + 1) * cothCF q (2 * i + 3) * (2 * i) + i * dN q (2 * i + 1) := by ring_nat
    _ ≤ (i + 1) * cothCF q (2 * i + 3) * dN q (2 * i + 2) + i * dN q (2 * i + 1) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hd2) _
    _ ≤ (i + 1) * cothCF q (2 * i + 3) * dN q (2 * i + 2)
        + (i + 1) * dN q (2 * i + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
    _ = (i + 1) * (cothCF q (2 * i + 3) * dN q (2 * i + 2) + dN q (2 * i + 1)) := by
        ring_nat

/-! ## §3 — packaging: `exp(2/q)` as an unconditional `CauchyCutSeq` -/

theorem e_cut_at_zero (q i m : Nat) : rcut (eNum q) (eDen q) i m 0 = true := by
  apply decide_eq_true
  exact Nat.le_trans (Nat.le_of_eq (Nat.mul_zero _)) (Nat.zero_le _)

/-- The cut is constant past `k + 2`. -/
theorem e_cut_const (q : Nat) (hq : 1 ≤ q) (m k : Nat) (hk : 1 ≤ k)
    (i j : Nat) (hi : k + 2 ≤ i) (hj : k + 2 ≤ j) :
    rcut (eNum q) (eDen q) i m k = rcut (eNum q) (eDen q) j m k :=
  rate_cut_const (eDen_pos q hq)
    (Htel_of_crossdet (fun L => 2 * cothCF q (2 * L + 3)) (e_hW q hq) (e_hcs q hq))
    (e_hmono q hq) (e_hmonoS q hq) m k hk i j hi hj

/-- ★★★★★ **`exp(2/q)` completes unconditionally** — the cut-Möbius step: the
    Lambert fold's odd convergents, transformed by `z ↦ (z+1)/(z−1)`, are a
    climbing convergent system with cross-determinant `2·a_{2L+3}`, so they carry
    the universal free total modulus `N(m,k) = k+2`.  The measure hypothesis of
    `ExpRationalCut.expPQCauchySep` is not needed on this presentation: `e^{2/q}`
    is a `Real213` Cauchy point with **no hypotheses beyond `q ≥ 1`**. -/
def expTwoOverQCFCauchySeq (q : Nat) (hq : 1 ≤ q) : CauchyCutSeq where
  cs := fun i => rcut (eNum q) (eDen q) i
  N := fun _ k => k + 2
  cauchy := by
    intro m k i j hi hj
    cases k with
    | zero =>
      show rcut (eNum q) (eDen q) i m 0 = rcut (eNum q) (eDen q) j m 0
      rw [e_cut_at_zero q i m, e_cut_at_zero q j m]
    | succ k' =>
      exact e_cut_const q hq m (k' + 1) (Nat.succ_le_succ (Nat.zero_le k')) i j hi hj

/-- Sanity anchors (`q = 1`): the Möbius convergents of `e²` run
    `7/1, 266/36, 27007/3655, …` (`e² ≈ 7.38906`), and the completed limit reads
    `false` at `22/3` and `true` at `37/5` — **`e² ∈ (22/3, 37/5] = (7.3̄, 7.4]`**,
    sharper than the series bracket `(7, 904/120]` and fully unconditional. -/
theorem exp_two_moebius_anchors :
    eNum 1 0 = 7 ∧ eDen 1 0 = 1 ∧ eNum 1 1 = 266 ∧ eDen 1 1 = 36
    ∧ (expTwoOverQCFCauchySeq 1 (Nat.le_refl 1)).limit 22 3 = false
    ∧ (expTwoOverQCFCauchySeq 1 (Nat.le_refl 1)).limit 37 5 = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpMoebius
