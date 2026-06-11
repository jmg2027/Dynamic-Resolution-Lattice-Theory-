import E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor
import E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake
import E213.Lib.Math.Analysis.CauchyComplete
import E213.Meta.Tactic.NatHelper

/-!
# ContinuedFractionModulus — every real ≥ 1 completes through its own continued fraction

`ContinuedFractionFloor` established the *universal det-one floor* (`cf_det_sq`) and the
two-step even cross-determinant `W'_{2n} = a_{2n+2}` (`cfDet2_even`).  Here those close the
final brick: the even-indexed convergents `p_{2n}/q_{2n}` of **any** real (partial quotients
`≥ 1`) satisfy the cross-determinant smallness bridge `CrossDetSmall`, hence carry a **free
total ∅-axiom modulus** — the real completes, with no irrationality measure, no LEM.

  * `cfPn` / `cfP_eq_cast` / `cfPn_pos` — the convergent numerators as `ℕ` (the `ℤ` `cfP` is
    their cast), positive when the quotients are `≥ 1`.
  * `cfDet2_even_nat` — the `ℕ` form of `cfDet2_even`: `p_{2n+2}·q_{2n} = p_{2n}·q_{2n+2} +
    a_{2n+2}` (the even two-step cross-determinant, descended from `ℤ` by injectivity).
  * `cfQn_ge_self` — `n ≤ q_n` (the Fibonacci floor in its crudest sufficient form), the
    growth that makes the smallness condition hold.
  * `mono_of_step` — **a single strict step ⟹ across-layer monotonicity** for any
    positive-denominator convergent system (the reusable `ratio_trans` chaining, generic).
  * ★★★ `cf_universal_total_modulus` — the even convergents of any real `≥ 1` carry a free
    total ∅-axiom modulus (`N(m,k) = k+2`).  `CrossDetConstDenom`'s φ-instance, lifted off
    the Fibonacci sequence onto an **arbitrary** partial-quotient sequence: the det-one floor
    is not special to φ, every real rides it.

The expansion engine reaches its terminus here: the floor's unit (`cf_det_sq`), amplified on
the even convergents to the partial quotient (`cfDet2_even`), is dominated by the
Fibonacci-growing denominator (`cfQn_ge_self`) — surplus fed back faster than it accrues, so
the residue closes.  Shift-invariance (a real and `real + 1` complete together) reduces every
real to a `≥ 1` representative, so "≥ 1" costs no generality.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus

open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor
  (cfP cfQ cfDet2 cfDet2_even cfQ_eq_cast cfQn cfQn_pos cfQn_fib)
open E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake (CrossDetSmall crossdet_small_total_modulus)
open E213.Lib.Math.NumberSystems.Real213.RateModulus (rcut)
open E213.Tactic.NatHelper (mul_assoc le_of_mul_le_mul_right mul_mul_mul_comm_213)

/-! ## §1 — the convergent numerators as `ℕ` -/

/-- Convergent numerators as a `ℕ` sequence (the `ℤ` `cfP` is their cast). -/
def cfPn (a : Nat → Nat) : Nat → Nat
  | 0   => a 0
  | 1   => a 1 * a 0 + 1
  | n+2 => a (n+2) * cfPn a (n+1) + cfPn a n

/-- `cfP` is the `ℤ`-cast of `cfPn`. -/
theorem cfP_eq_cast (a : Nat → Nat) : ∀ n, cfP a n = (cfPn a n : Int)
  | 0   => rfl
  | 1   => by
      show (a 1 : Int) * (a 0 : Int) + 1 = ((a 1 * a 0 + 1 : Nat) : Int)
      rw [Int.ofNat_add, Int.ofNat_mul]; rfl
  | n+2 => by
      show (a (n+2) : Int) * cfP a (n+1) + cfP a n
            = ((a (n+2) * cfPn a (n+1) + cfPn a n : Nat) : Int)
      rw [Int.ofNat_add, Int.ofNat_mul, cfP_eq_cast a (n+1), cfP_eq_cast a n]

/-- The numerators are positive (partial quotients `≥ 1`). -/
theorem cfPn_pos (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) : ∀ n, 1 ≤ cfPn a n
  | 0   => ha 0
  | 1   => Nat.le_add_left 1 _
  | n+2 => Nat.le_trans (cfPn_pos a ha n) (Nat.le_add_left _ _)

/-! ## §2 — the even two-step cross-determinant over `ℕ` -/

/-- `X + (−Y) = Z ⟹ X = Y + Z` over `ℤ` (the descent rearrangement). -/
private theorem int_eq_of_add_neg {X Y a : Int} (h : X + -Y = a) : X = Y + a := by
  have e : Y + a = X := by
    rw [← h, ← E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm Y X,
        E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_neg_cancel, Int.add_zero]
  exact e.symm

/-- ★★ **The even two-step cross-determinant over `ℕ`.**  `p_{2n+2}·q_{2n} = p_{2n}·q_{2n+2}
    + a_{2n+2}` — `cfDet2_even` descended from `ℤ` by `ofNat` injectivity. -/
theorem cfDet2_even_nat (a : Nat → Nat) (n : Nat) :
    cfPn a (2*n + 2) * cfQn a (2*n) = cfPn a (2*n) * cfQn a (2*n + 2) + a (2*n + 2) := by
  have h : cfP a (2*n + 2) * cfQ a (2*n) + -(cfP a (2*n) * cfQ a (2*n + 2))
            = (a (2*n + 2) : Int) := cfDet2_even a n
  rw [cfP_eq_cast a (2*n + 2), cfQ_eq_cast a (2*n), cfP_eq_cast a (2*n),
      cfQ_eq_cast a (2*n + 2)] at h
  have h3 := int_eq_of_add_neg h
  have goal_int : (↑(cfPn a (2*n + 2) * cfQn a (2*n)) : Int)
                = ↑(cfPn a (2*n) * cfQn a (2*n + 2) + a (2*n + 2)) := by
    rw [Int.ofNat_mul, Int.ofNat_add, Int.ofNat_mul]; exact h3
  exact Int.ofNat.inj goal_int

/-! ## §3 — the denominators outgrow the index -/

/-- `n ≤ q_n` (the crudest Fibonacci floor that suffices for smallness). -/
theorem cfQn_ge_self (a : Nat → Nat) (ha : ∀ i, 1 ≤ a (i+1)) : ∀ n, n ≤ cfQn a n
  | 0   => Nat.zero_le _
  | 1   => ha 0
  | n+2 => by
      have h1 : (n+1) + 1 ≤ cfQn a (n+1) + cfQn a n :=
        Nat.add_le_add (cfQn_ge_self a ha (n+1)) (cfQn_pos a ha n)
      exact Nat.le_trans h1 (cfQn_fib a ha n)

/-! ## §4 — across-layer monotonicity from a single strict step (reusable) -/

private theorem rearr (w x y z : Nat) : (w*x)*(y*z) = (w*z)*(y*x) := by
  rw [mul_mul_mul_comm_213 w x y z, mul_mul_mul_comm_213 w z y x, Nat.mul_comm x z]

/-- One-step ratio monotonicity composes across a middle index `M` (positive-denominator
    cross-multiplication cancellation) — generic over any convergent system. -/
theorem ratio_trans_gen {a d : Nat → Nat} (hpos : ∀ i, 0 < a i * d i)
    (N M i : Nat) (h1 : a N * d M ≤ a M * d N) (h2 : a M * d i ≤ a i * d M) :
    a N * d i ≤ a i * d N := by
  have key : (a N * d i) * (a M * d M) ≤ (a i * d N) * (a M * d M) := by
    calc (a N * d i) * (a M * d M)
        = (a N * d M) * (a M * d i) := rearr (a N) (d i) (a M) (d M)
      _ ≤ (a M * d N) * (a i * d M) := Nat.mul_le_mul h1 h2
      _ = (a i * d N) * (a M * d M) := by
          rw [mul_mul_mul_comm_213 (a M) (d N) (a i) (d M),
              Nat.mul_comm (a M) (a i),
              mul_mul_mul_comm_213 (a i) (a M) (d N) (d M),
              rearr (a i) (d N) (a M) (d M)]
  exact le_of_mul_le_mul_right (hpos M) key

/-- ★ **A single strict step ⟹ across-layer monotonicity.**  For any positive-denominator
    convergent system with `a_n·d_{n+1} ≤ a_{n+1}·d_n` at every step, the convergents are
    monotone across arbitrary layers: `N ≤ i ⟹ a_N·d_i ≤ a_i·d_N`. -/
theorem mono_of_step {a d : Nat → Nat} (hpos : ∀ i, 0 < a i * d i)
    (step : ∀ n, a n * d (n+1) ≤ a (n+1) * d n) :
    ∀ N i, N ≤ i → a N * d i ≤ a i * d N := by
  intro N i hNi
  obtain ⟨t, rfl⟩ := Nat.le.dest hNi
  induction t with
  | zero => exact Nat.le_of_eq (by rw [Nat.add_zero])
  | succ s ih =>
    rw [show N + (s+1) = (N+s) + 1 from rfl]
    exact ratio_trans_gen hpos N (N+s) ((N+s)+1) (ih (Nat.le_add_right N s)) (step (N+s))

/-! ## §5 — the even convergents, and universal completion -/

/-- The even-indexed convergent numerators `p_{2n}` of `a`. -/
def cfEvenNum (a : Nat → Nat) (n : Nat) : Nat := cfPn a (2*n)

/-- The even-indexed convergent denominators `q_{2n}` of `a`. -/
def cfEvenDen (a : Nat → Nat) (n : Nat) : Nat := cfQn a (2*n)

theorem cf_hd (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) (i : Nat) : 1 ≤ cfEvenDen a i :=
  cfQn_pos a (fun j => ha (j+1)) (2*i)

theorem cf_hpos (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) (i : Nat) :
    0 < cfEvenNum a i * cfEvenDen a i :=
  Nat.mul_pos (cfPn_pos a ha (2*i)) (cfQn_pos a (fun j => ha (j+1)) (2*i))

/-- The even-convergent recurrence-determinant `W'_n = a_{2n+2}` (the `hW` of the bridge). -/
theorem cf_hW (a : Nat → Nat) (i : Nat) :
    cfEvenNum a (i+1) * cfEvenDen a i
      = cfEvenNum a i * cfEvenDen a (i+1) + a (2*i + 2) := by
  show cfPn a (2*(i+1)) * cfQn a (2*i)
        = cfPn a (2*i) * cfQn a (2*(i+1)) + a (2*i + 2)
  rw [show 2*(i+1) = 2*i + 2 from by rw [Nat.mul_succ]]
  exact cfDet2_even_nat a i

/-- The even convergents are *strictly* increasing (`a_{2n+2} ≥ 1` is the gap). -/
theorem cf_hmonoS (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) (i : Nat) :
    cfEvenNum a i * cfEvenDen a (i+1) < cfEvenNum a (i+1) * cfEvenDen a i := by
  show cfPn a (2*i) * cfQn a (2*(i+1)) < cfPn a (2*(i+1)) * cfQn a (2*i)
  rw [show 2*(i+1) = 2*i + 2 from by rw [Nat.mul_succ], cfDet2_even_nat a i]
  exact Nat.lt_add_of_pos_right (ha (2*i + 2))

/-- The smallness condition holds at every `i`: the partial quotient `a_{2i+2}` over the
    denominator's growth (`i ≤ q_{2i+1}`). -/
theorem cf_hcs (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) :
    CrossDetSmall (fun i => a (2*i + 2)) (cfEvenDen a) := by
  intro i _
  show i*(i+1) * a (2*i + 2) + i * cfQn a (2*i) ≤ (i+1) * cfQn a (2*(i+1))
  rw [show 2*(i+1) = 2*i + 2 from by rw [Nat.mul_succ],
      show cfQn a (2*i + 2) = a (2*i + 2) * cfQn a (2*i + 1) + cfQn a (2*i) from rfl,
      Nat.mul_add (i+1) (a (2*i + 2) * cfQn a (2*i + 1)) (cfQn a (2*i))]
  have hile : i ≤ cfQn a (2*i + 1) :=
    Nat.le_trans
      (by rw [Nat.two_mul]; exact Nat.le_trans (Nat.le_add_right i i) (Nat.le_succ _))
      (cfQn_ge_self a (fun j => ha (j+1)) (2*i + 1))
  apply Nat.add_le_add
  · calc i*(i+1) * a (2*i + 2)
        = ((i+1) * a (2*i + 2)) * i := by
            rw [mul_assoc, Nat.mul_comm i ((i+1) * a (2*i + 2))]
      _ ≤ ((i+1) * a (2*i + 2)) * cfQn a (2*i + 1) :=
            Nat.mul_le_mul_left ((i+1) * a (2*i + 2)) hile
      _ = (i+1) * (a (2*i + 2) * cfQn a (2*i + 1)) := mul_assoc _ _ _
  · exact Nat.mul_le_mul_right (cfQn a (2*i)) (Nat.le_succ i)

theorem cf_hmono (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) :
    ∀ N i, N ≤ i → cfEvenNum a N * cfEvenDen a i ≤ cfEvenNum a i * cfEvenDen a N :=
  mono_of_step (cf_hpos a ha) (fun n => Nat.le_of_lt (cf_hmonoS a ha n))

/-- ★★★ **Universal completion through the continued fraction.**  For any real `≥ 1`
    (partial quotients `a_i ≥ 1`), the even-indexed convergents `p_{2n}/q_{2n}` carry a free
    total ∅-axiom modulus `N(m,k) = k+2`: the real completes, with no irrationality measure
    and no LEM.  This is `CrossDetConstDenom.phi_total_modulus_via_const` for φ, lifted off
    the Fibonacci sequence onto an arbitrary partial-quotient sequence — the det-one floor of
    `cf_det_sq` is the universal best-approximation locus, and every real rides it. -/
theorem cf_universal_total_modulus (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (cfEvenNum a) (cfEvenDen a) i m k = rcut (cfEvenNum a) (cfEvenDen a) j m k :=
  crossdet_small_total_modulus (fun i => a (2*i + 2))
    (cf_hd a ha) (cf_hW a) (cf_hcs a ha) (cf_hmono a ha) (cf_hmonoS a ha) m k hk


/-! ## §6 — packaging: the `CauchyCutSeq`, and the Lambert transcendental instance

`cf_universal_total_modulus` delivers the modulus existentially; here it is packaged
with the **explicit** constant (`N(m,k) = k+2`, via `rate_cut_const`) into a genuine
`CauchyCutSeq` — and instantiated at the first *transcendental* CF in the repo:
Lambert's continued fraction `coth(1/q) = [q; 3q, 5q, 7q, …]` (all partial quotients
`(2n+1)·q ≥ 1`, so the `≥ 1` hypothesis is free).  The CF pointing carries everything:
no measure, no rate hypothesis — contrast `ExpUnitModulus.exp_pq_no_htel`, where the
*series* pointing of `exp(p/q)` (`p ≥ 2`) provably carries nothing.

**The weld (recorded open)**: that the Lambert real *equals* `coth(1/q)` as a series
object (CF correctness — the Padé/Bessel identity) is not proven here; once welded,
`e^{2/q} = (coth(1/q) + 1)/(coth(1/q) − 1)` is one cut-Möbius step away — the sharpest
route to discharging `ExpRationalCut`'s measure hypothesis
(`modulus_degree_ladder.md`). -/

open E213.Lib.Math.NumberSystems.Real213.RateModulus (rate_cut_const Htel_of_crossdet)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-- Resolution-`0` probes read `true` at every layer. -/
theorem cf_cut_at_zero (a : Nat → Nat) (i m : Nat) :
    rcut (cfEvenNum a) (cfEvenDen a) i m 0 = true := by
  apply decide_eq_true
  exact Nat.le_trans (Nat.le_of_eq (Nat.mul_zero _)) (Nat.zero_le _)

/-- **The CF cut is constant past `k+2`** — `cf_universal_total_modulus` with the
    explicit constant. -/
theorem cf_cut_const (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) (m k : Nat) (hk : 1 ≤ k)
    (i j : Nat) (hi : k + 2 ≤ i) (hj : k + 2 ≤ j) :
    rcut (cfEvenNum a) (cfEvenDen a) i m k = rcut (cfEvenNum a) (cfEvenDen a) j m k :=
  rate_cut_const (cf_hd a ha)
    (Htel_of_crossdet (fun i => a (2*i + 2)) (cf_hW a) (cf_hcs a ha))
    (cf_hmono a ha) (cf_hmonoS a ha) m k hk i j hi hj

/-- ★★★★★ **Every explicitly presented continued fraction is a `Real213` Cauchy
    point, unconditionally**: the even-convergent cut sequence with the constructed
    total modulus `N(m,k) = k+2`.  The CF pointing is universally rate-carrying. -/
def cfCauchySeq (a : Nat → Nat) (ha : ∀ i, 1 ≤ a i) : CauchyCutSeq where
  cs := fun i => rcut (cfEvenNum a) (cfEvenDen a) i
  N := fun _ k => k + 2
  cauchy := by
    intro m k i j hi hj
    cases k with
    | zero =>
      show rcut (cfEvenNum a) (cfEvenDen a) i m 0
          = rcut (cfEvenNum a) (cfEvenDen a) j m 0
      rw [cf_cut_at_zero a i m, cf_cut_at_zero a j m]
    | succ k' =>
      exact cf_cut_const a ha m (k' + 1) (Nat.succ_le_succ (Nat.zero_le k')) i j hi hj

/-- Lambert's continued fraction of `coth(1/q)`: partial quotients `(2n+1)·q`
    (`[q; 3q, 5q, 7q, …]`). -/
def cothCF (q : Nat) (n : Nat) : Nat := (2 * n + 1) * q

theorem cothCF_pos (q : Nat) (hq : 1 ≤ q) : ∀ n, 1 ≤ cothCF q n := fun n =>
  Nat.le_trans hq (Nat.le_mul_of_pos_left q (Nat.succ_pos (2 * n)))

/-- ★★★★ **The Lambert real `[q; 3q, 5q, …]` completes unconditionally** — the CF
    presentation of `coth(1/q)`, a transcendental, as a genuine `CauchyCutSeq` with
    total modulus `k+2` and no hypotheses beyond `q ≥ 1`. -/
def cothUnitCFCauchySeq (q : Nat) (hq : 1 ≤ q) : CauchyCutSeq :=
  cfCauchySeq (cothCF q) (cothCF_pos q hq)

/-- Sanity anchors for the Lambert `coth(1)` fold `[1; 3, 5, 7, …]`
    (`coth(1) = (e²+1)/(e²−1) ≈ 1.31303…`): the convergents run
    `1/1, 4/3, 21/16, 151/115, …`, and the completed cut reads `true` at `3/2`
    (`coth(1) ≤ 3/2`) and `false` at `5/4` (`coth(1) > 5/4`). -/
theorem coth1_anchors :
    cfPn (cothCF 1) 2 = 21 ∧ cfQn (cothCF 1) 2 = 16
    ∧ (cothUnitCFCauchySeq 1 (Nat.le_refl 1)).limit 3 2 = true
    ∧ (cothUnitCFCauchySeq 1 (Nat.le_refl 1)).limit 5 4 = false :=
  ⟨by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
