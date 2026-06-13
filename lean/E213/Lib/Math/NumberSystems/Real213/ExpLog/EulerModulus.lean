import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut
import E213.Lib.Math.NumberSystems.Real213.HolonomicReal
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus
import E213.Lib.Math.Analysis.Cauchy.EulerDivergenceForm
import E213.Meta.Nat.PolyNat

/-!
# EulerModulus — e has a TOTAL constructive (∅-axiom) cut modulus `N(m,k) = k+2`

e is the structured-transcendental instance of the general generator
`RateModulus.rate_total_modulus`: a real whose convergents `a_i/d_i` carry a rate that
beats their denominator growth completes with a *constructed* total modulus.  e's
convergents are `eulerNum i / eulerDen i = a_i/i!`, and everything the generator asks
for is supplied by e's recurrence:

  * the convergents increase (`euler_hmono`, `euler_hmonoS`);
  * the rate certificate `Htel` holds — and it holds *because* e's cross-determinant
    is exactly `eulerDen` (`euler_cross_det`), so `RateModulus.Htel_of_crossdet` reduces
    it to `i(i+1)+i ≤ (i+1)²` (`0 ≤ 1`, via the `PolyNat` ring).  This is the
    divergence-ladder's cross-determinant feeding directly into the rate.

So `eulerCut i m k` is **constant for `i ≥ k+2`, uniformly in `(m,k)`** with `k ≥ 1`
(`euler_cut_const`): `N(m,k) = k+2` is a total ∅-axiom modulus, putting the structured
transcendental e on the same constructive footing as the algebraic φ
(`eHolonomicReal`).  The general "monotone-bounded ⟹ Cauchy needs LEM" obstruction
(`MonotonicBounded`) is for *rate-free* sequences and does not bind here.

Narrative: `theory/math/analysis/holonomic_modulus.md`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus
open E213.Lib.Math.NumberSystems.Real213.Modulus

open E213.Meta.Nat.PolyNat (poly_id)
open E213.Tactic.NatHelper (add_mul mul_assoc add_sub_of_le)
open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen eulerDen_pos)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut (eulerCut eulerCut_eq)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (Htel Htel_of_crossdet rate_cut_const)
open E213.Lib.Math.Analysis.Cauchy.EulerDivergenceForm (euler_cross_det)

/-! ## §1 — e's convergents increase -/

/-- e's convergents are strictly increasing: `eᵢ < eᵢ₊₁` (cross-multiplied).  The
    difference is exactly `eulerDen i`. -/
theorem euler_hmonoS (i : Nat) :
    eulerNum i * eulerDen (i+1) < eulerNum (i+1) * eulerDen i := by
  show eulerNum i * ((i+1)*eulerDen i) < ((i+1)*eulerNum i+1)*eulerDen i
  have hL : eulerNum i * ((i+1)*eulerDen i) = (i+1)*eulerNum i*eulerDen i := by
    rw [← mul_assoc, Nat.mul_comm (eulerNum i) (i+1)]
  have hR : ((i+1)*eulerNum i+1)*eulerDen i = (i+1)*eulerNum i*eulerDen i + eulerDen i := by
    rw [add_mul ((i+1)*eulerNum i) 1 (eulerDen i), Nat.one_mul]
  rw [hL, hR]; exact Nat.lt_add_of_pos_right (eulerDen_pos i)

/-- e's convergents are increasing across any gap (iterated, cross-multiplied). -/
theorem euler_hmono (N : Nat) :
    ∀ i, N ≤ i → eulerNum N * eulerDen i ≤ eulerNum i * eulerDen N := by
  have aux : ∀ t, eulerNum N * eulerDen (N+t) ≤ eulerNum (N+t) * eulerDen N := by
    intro t
    induction t with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      show eulerNum N * ((N+t+1)*eulerDen (N+t)) ≤ ((N+t+1)*eulerNum (N+t)+1)*eulerDen N
      have h1 : eulerNum N * ((N+t+1)*eulerDen (N+t))
          = (N+t+1)*(eulerNum N*eulerDen (N+t)) := by
        rw [← mul_assoc, Nat.mul_comm (eulerNum N) (N+t+1), mul_assoc]
      have h3 : (N+t+1)*(eulerNum (N+t)*eulerDen N)
          ≤ ((N+t+1)*eulerNum (N+t)+1)*eulerDen N := by
        have hLr : (N+t+1)*(eulerNum (N+t)*eulerDen N)
            = (N+t+1)*eulerNum (N+t)*eulerDen N := (mul_assoc _ _ _).symm
        have hRr : ((N+t+1)*eulerNum (N+t)+1)*eulerDen N
            = (N+t+1)*eulerNum (N+t)*eulerDen N + eulerDen N := by
          rw [add_mul ((N+t+1)*eulerNum (N+t)) 1 (eulerDen N), Nat.one_mul]
        rw [hLr, hRr]; exact Nat.le_add_right _ _
      rw [h1]
      exact Nat.le_trans (Nat.mul_le_mul_left (N+t+1) ih) h3
  intro i hi; rw [← add_sub_of_le hi]; exact aux (i - N)

/-! ## §2 — the rate certificate, via the cross-determinant -/

/-- ★★ **e satisfies the rate certificate `Htel`, via its cross-determinant.**
    e's cross-determinant is exactly `eulerDen` (`euler_cross_det`:
    `eulerNum (n+1)·eulerDen n = eulerNum n·eulerDen (n+1) + eulerDen n`), so the
    bridge `RateModulus.Htel_of_crossdet` applies with `W = eulerDen`; the remaining
    condition `i(i+1)·eulerDen i + i·eulerDen i ≤ (i+1)·eulerDen (i+1)` reduces to
    `i(i+1)+i ≤ (i+1)²` (i.e. `0 ≤ 1`, via the `PolyNat` ring).  This is the
    depth-arc cross-determinant feeding directly into the rate certificate. -/
theorem euler_Htel : Htel eulerNum eulerDen :=
  Htel_of_crossdet eulerDen (fun i => euler_cross_det i) (fun i _ => by
    show i*(i+1)*eulerDen i + i*eulerDen i ≤ (i+1)*eulerDen (i+1)
    rw [show eulerDen (i+1) = (i+1)*eulerDen i from rfl, ← add_mul, ← mul_assoc]
    refine Nat.mul_le_mul_right (eulerDen i) ?_
    have h : (i+1)*(i+1) = i*(i+1)+i+1 :=
      poly_id (.mul (.add .X (.C 1)) (.add .X (.C 1)))
              (.add (.add (.mul .X (.add .X (.C 1))) .X) (.C 1)) rfl i
    rw [h]; exact Nat.le_succ _)

/-! ## §3 — e's total modulus (from the general generator) -/

/-- ★★★ **e's cut is constant past `k+2`** — `eulerCut i m k = eulerCut j m k` for all
    `i, j ≥ k+2` (`k ≥ 1`).  Direct instance of `RateModulus.rate_cut_const` at e's
    convergents (`rcut eulerNum eulerDen = eulerCut` via `eulerCut_eq`). -/
theorem euler_cut_const (m k : Nat) (hk : 1 ≤ k) (i j : Nat)
    (hi : k + 2 ≤ i) (hj : k + 2 ≤ j) : eulerCut i m k = eulerCut j m k := by
  rw [eulerCut_eq i m k, eulerCut_eq j m k]
  exact rate_cut_const eulerDen_pos euler_Htel euler_hmono euler_hmonoS m k hk i j hi hj

/-- ★★★ **e's total ∅-axiom cut modulus.**  For every `(m,k)` with `k ≥ 1` the cut is
    constant past `N = k+2` — e's cut Cauchy property holds at *every* `(m,k)`, no LEM,
    no irrationality measure. -/
theorem euler_total_modulus (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → eulerCut i m k = eulerCut j m k :=
  ⟨k+2, fun i j hi hj => euler_cut_const m k hk i j hi hj⟩

/-! ## §4 — e as a `HolonomicReal` with a constructed total modulus -/

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut (eulerCut_valid)

/-- At `k = 0` the cut is `true` at every layer (`eulerNum i · 0 = 0 ≤ _`). -/
private theorem eulerCut_at_zero (i m : Nat) : eulerCut i m 0 = true := by
  rw [eulerCut_eq]; apply decide_eq_true
  show eulerNum i * 0 ≤ eulerDen i * m
  rw [Nat.mul_zero]; exact Nat.zero_le _

/-- ★★★ **e's convergent cut-sequence with its constructed total modulus
    `N(m,k) = k+2`.**  The Cauchy field is discharged uniformly: `k = 0` is constant
    `true`, `k ≥ 1` is `euler_cut_const`.  No modulus hypothesis. -/
def eulerCauchySeq : CauchyCutSeq where
  cs := eulerCut
  N := fun _ k => k + 2
  cauchy := by
    intro m k i j hi hj
    cases k with
    | zero => rw [eulerCut_at_zero i m, eulerCut_at_zero j m]
    | succ k' =>
      exact euler_cut_const m (k'+1) (Nat.succ_le_succ (Nat.zero_le k')) i j hi hj

/-- e's holonomic recurrence: order 1, the degree-1 coefficient `c(n) = n+1`
    (`eulerDen (n+1) = (n+1)·eulerDen n`, `eulerNum (n+1) = (n+1)·eulerNum n + 1`). -/
def eHolonomic : E213.Lib.Math.NumberSystems.Real213.Holonomic where
  order := 1
  coeff := fun n => (n : Int) + 1
  cdeg  := fun _ => 1
  init  := fun _ => 1

/-- ★★★ **e is a complete `HolonomicReal`** — like φ, with the convergence modulus a
    *constructed field* (`eulerCauchySeq.N = k+2`), not a hypothesis.  The structured
    transcendental e inhabits the unconditional real API ∅-axiom: the general
    generator extends past the algebraic floor to (at least) the degree-1 holonomic
    class. -/
def eHolonomicReal : E213.Lib.Math.NumberSystems.Real213.HolonomicReal where
  hol   := eHolonomic
  seq   := eulerCauchySeq
  valid := CauchyCutSeq.limit_valid eulerCauchySeq (fun i => eulerCut_valid i)

/-- ★★ **`eHolonomic` is the genuine recurrence, not decoration.**  e's convergent
    denominators and numerators satisfy the order-1 P-recursive recurrence whose
    coefficient is `eHolonomic.coeff n = (n:Int)+1` (degree 1): `eulerDen (n+1) =
    (n+1)·eulerDen n` and `eulerNum (n+1) = (n+1)·eulerNum n + 1`.  So
    `eHolonomicReal.hol` actually generates the cut-sequence `eHolonomicReal.seq`. -/
theorem eHolonomic_recurrence (n : Nat) :
    eHolonomic.coeff n = (n : Int) + 1 ∧
    eulerDen (n+1) = (n+1) * eulerDen n ∧
    eulerNum (n+1) = (n+1) * eulerNum n + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- e's holonomic cut is the convergent read at the modulus index: `eulerCut (k+2)`. -/
theorem eHolonomicReal_cut (m k : Nat) :
    eHolonomicReal.cut m k = eulerCut (k+2) m k := rfl

/-- ★★ **The holonomic cut is the stable convergent value.**  For `k ≥ 1` and any
    `i ≥ k+2`, e's `HolonomicReal` cut equals `eulerCut i m k` — the limit object is
    exactly the (constant) tail value of the convergents.  The e analogue of
    `phiHolonomicReal_cut`. -/
theorem eHolonomicReal_cut_stable (m k : Nat) (hk : 1 ≤ k) (i : Nat) (hi : k+2 ≤ i) :
    eHolonomicReal.cut m k = eulerCut i m k := by
  rw [eHolonomicReal_cut]; exact euler_cut_const m k hk (k+2) i (Nat.le_refl _) hi

end E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus
