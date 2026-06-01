import E213.Lib.Math.Real213.ExpLog.EulerCut
import E213.Lib.Math.Real213.HolonomicReal
import E213.Lib.Math.Real213.RateModulus
import E213.Lib.Math.Cauchy.EulerDivergenceForm
import E213.Meta.Nat.PolyNat

/-!
# EulerModulus — e has a TOTAL constructive (∅-axiom) cut modulus `N(m,k) = k+2`

e's convergents `e_i = eulerNum i / eulerDen i = a_i/i!` carry explicit factorial
denominators and a known tail rate.  That structure yields a *total* per-`(m,k)`
convergence modulus for e's cut, constructively — the general "monotone-bounded ⟹
Cauchy needs LEM" obstruction (`MonotonicBounded`) is for *rate-free* sequences and
does not bind here.

**The mechanism.**  Carry the margin invariant `e_i + 1/(i·i!) ≤ m/k` (`euler_inv`).
Its forward step needs only `i(i+2) ≤ (i+1)²` (i.e. `0 ≤ 1`, discharged by the
`PolyNat` reflection prover) — the tail estimate is a trivial induction.  Compared at
index `k+1`, the denominator gap `|m/k − e_{k+1}| ≥ 1/(k·(k+1)!)` exceeds the entire
future variation `< 1/((k+1)·(k+1)!)`, so the cut is constant past `k+1` (or `k+2` in
the boundary case `m/k = e_{k+1}`).

So `eulerCut i m k` is **constant for `i ≥ k+2`, uniformly in `(m,k)`** with `k ≥ 1`
(`euler_cut_const`): `N(m,k) = k+2` is a total ∅-axiom modulus, putting the
structured transcendental e on the same constructive footing as the algebraic φ.

The choice of side (e `<`/`>` `m/k`) is *not* a smuggled LEM: it is read off
`eulerCut (k+1) m k`, a decidable `Bool`, because the gap exceeds the approximation
error — exactly what a rate-free sequence lacks.

Narrative: `theory/math/analysis/holonomic_modulus.md`.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.ExpLog.EulerModulus

open E213.Meta.Nat.PolyNat (poly_id)
open E213.Tactic.NatHelper (add_mul mul_assoc le_of_mul_le_mul_right add_sub_of_le)
open E213.Lib.Math.Cauchy.EulerSeq (eulerNum eulerDen eulerDen_pos)
open E213.Lib.Math.Real213.ExpLog.EulerCut (eulerCut eulerCut_eq eAb)
open E213.Lib.Math.Real213.AbCutSeq (cut_false_fwd)

/-! ## §1 — the margin-invariant engine -/

/-- The one nonlinear fact the induction needs: `i(i+2) ≤ (i+1)²` (i.e. `0 ≤ 1`),
    discharged by the `PolyNat` reflection ring. -/
private theorem key_step_ineq (i : Nat) : i * (i + 2) ≤ (i + 1) * (i + 1) := by
  have h : (i + 1) * (i + 1) = i * (i + 2) + 1 :=
    poly_id (.mul (.add .X (.C 1)) (.add .X (.C 1)))
            (.add (.mul .X (.add .X (.C 2))) (.C 1)) rfl i
  rw [h]; exact Nat.le_succ _

private theorem L_base (x k : Nat) : (x*(k+1)+1)*k ≤ (x*k+1)*(k+1) := by
  have l1 : (x*(k+1)+1)*k = x*(k+1)*k + k := by rw [add_mul, Nat.one_mul]
  have l2 : (x*k+1)*(k+1) = x*(k+1)*k + (k+1) := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_assoc, Nat.mul_comm k (k+1), ← mul_assoc]
  rw [l1, l2]; exact Nat.add_le_add_left (Nat.le_succ k) _

private theorem L_step (a i : Nat) :
    (((i+1)*(i+1))*a + (i+2)) * i ≤ (a*i + 1) * ((i+1)*(i+1)) := by
  have hL : (((i+1)*(i+1))*a + (i+2)) * i = a*i*((i+1)*(i+1)) + i*(i+2) := by
    rw [add_mul, Nat.mul_comm (i+2) i]; congr 1
    rw [Nat.mul_comm ((i+1)*(i+1)) a, mul_assoc, Nat.mul_comm ((i+1)*(i+1)) i, ← mul_assoc]
  have hR : (a*i + 1) * ((i+1)*(i+1)) = a*i*((i+1)*(i+1)) + (i+1)*(i+1) := by
    rw [add_mul, Nat.one_mul]
  rw [hL, hR]; exact Nat.add_le_add_left (key_step_ineq i) _

private theorem swap_kr (P k i : Nat) : (P*k)*i = (P*i)*k := by
  rw [mul_assoc, Nat.mul_comm k i, ← mul_assoc]

private theorem reorder_mid (m i D s : Nat) : (m*(i*D))*s = (m*(s*D))*i := by
  rw [mul_assoc m (i*D) s, mul_assoc m (s*D) i]; congr 1
  rw [Nat.mul_comm (i*D) s, ← mul_assoc, mul_assoc s D i, Nat.mul_comm D i, ← mul_assoc]

/-- The margin invariant `e_i + 1/(i·i!) ≤ m/k`, cross-multiplied to `Nat`. -/
abbrev EInv (m k i : Nat) : Prop := (eulerNum i * i + 1) * k ≤ m * (i * eulerDen i)

/-- The inductive step: the margin invariant is preserved (`PolyNat`-trivial step). -/
private theorem euler_inv_step (m k i : Nat) (hi1 : 1 ≤ i) (ih : EInv m k i) :
    EInv m k (i+1) := by
  show (eulerNum (i+1)*(i+1)+1)*k ≤ m*((i+1)*eulerDen (i+1))
  have hnum : eulerNum (i+1)*(i+1)+1 = ((i+1)*(i+1))*eulerNum i + (i+2) := by
    show ((i+1)*eulerNum i+1)*(i+1)+1 = ((i+1)*(i+1))*eulerNum i + (i+2)
    rw [add_mul, Nat.one_mul,
        show (i+1)*eulerNum i*(i+1) = ((i+1)*(i+1))*eulerNum i from by
          rw [Nat.mul_comm (i+1) (eulerNum i), mul_assoc,
              Nat.mul_comm (eulerNum i) ((i+1)*(i+1))], Nat.add_assoc]
  have hden : (i+1)*eulerDen (i+1) = ((i+1)*(i+1))*eulerDen i := by
    show (i+1)*((i+1)*eulerDen i) = ((i+1)*(i+1))*eulerDen i
    rw [← mul_assoc]
  rw [hnum, hden]
  have hki : ((((i+1)*(i+1))*eulerNum i + (i+2))*k)*i ≤ (m*(((i+1)*(i+1))*eulerDen i))*i :=
    calc ((((i+1)*(i+1))*eulerNum i + (i+2))*k)*i
        = ((((i+1)*(i+1))*eulerNum i + (i+2))*i)*k := swap_kr _ k i
      _ ≤ ((eulerNum i*i+1)*((i+1)*(i+1)))*k := Nat.mul_le_mul_right k (L_step (eulerNum i) i)
      _ = ((eulerNum i*i+1)*k)*((i+1)*(i+1)) := swap_kr _ ((i+1)*(i+1)) k
      _ ≤ (m*(i*eulerDen i))*((i+1)*(i+1)) := Nat.mul_le_mul_right _ ih
      _ = (m*(((i+1)*(i+1))*eulerDen i))*i := reorder_mid m i (eulerDen i) ((i+1)*(i+1))
  exact le_of_mul_le_mul_right hi1 hki

/-- The margin invariant holds for every `i ≥ k+1`, given the strict bracket
    `e_{k+1} < m/k`.  Induction on `t` with `i = k+1+t` (`Nat.le_induction` is
    Mathlib-only). -/
private theorem euler_inv (m k : Nat)
    (hstrict : eulerNum (k+1) * k + 1 ≤ eulerDen (k+1) * m) :
    ∀ i, k + 1 ≤ i → EInv m k i := by
  have aux : ∀ t, EInv m k (k+1+t) := by
    intro t
    induction t with
    | zero =>
      show (eulerNum (k+1)*(k+1)+1)*k ≤ m*((k+1)*eulerDen (k+1))
      have e2 : (eulerNum (k+1)*k+1)*(k+1) ≤ (eulerDen (k+1)*m)*(k+1) :=
        Nat.mul_le_mul_right (k+1) hstrict
      have e3 : (eulerDen (k+1)*m)*(k+1) = m*((k+1)*eulerDen (k+1)) := by
        rw [Nat.mul_comm (eulerDen (k+1)) m, mul_assoc, Nat.mul_comm (eulerDen (k+1)) (k+1)]
      exact Nat.le_trans (L_base (eulerNum (k+1)) k) (e3 ▸ e2)
    | succ t ih =>
      have hi1 : 1 ≤ k+1+t :=
        Nat.le_trans (Nat.le_add_left 1 k) (Nat.le_add_right (k+1) t)
      exact euler_inv_step m k (k+1+t) hi1 ih
  intro i hi
  rw [← add_sub_of_le hi]
  exact aux (i - (k+1))

/-! ## §2 — invariant ⟹ cut, and the false side -/

/-- The margin invariant forces the cut `true` (constructive left-cancel). -/
private theorem euler_inv_cut (m k i : Nat) (hk : 1 ≤ k) (hinv : EInv m k i) :
    eulerCut i m k = true := by
  rw [eulerCut_eq]; apply decide_eq_true
  have h1 : (eulerNum i*i)*k + k ≤ m*(i*eulerDen i) := by
    have e : (eulerNum i*i+1)*k = (eulerNum i*i)*k + k := by rw [add_mul, Nat.one_mul]
    rw [← e]; exact hinv
  have h2 : (eulerNum i*i)*k + 1 ≤ m*(i*eulerDen i) :=
    Nat.le_trans (Nat.add_le_add_left hk _) h1
  have el : (eulerNum i*i)*k = i*(eulerNum i*k) := by
    rw [Nat.mul_comm (eulerNum i) i, mul_assoc]
  have er : m*(i*eulerDen i) = i*(m*eulerDen i) := by
    rw [← mul_assoc, Nat.mul_comm m i, mul_assoc]
  rw [el, er] at h2
  have h4 : eulerNum i*k < m*eulerDen i := by
    rcases Nat.lt_or_ge (eulerNum i*k) (m*eulerDen i) with h | h
    · exact h
    · exact absurd (E213.Tactic.NatHelper.lt_of_lt_le h2 (Nat.mul_le_mul_left i h))
        (Nat.lt_irrefl _)
  rw [Nat.mul_comm (eulerDen i) m]; exact Nat.le_of_lt h4

/-- `false` propagates forward (`e_i` increasing) — `eulerCut`-level wrapper of
    `AbCutSeq.cut_false_fwd`. -/
private theorem euler_false_fwd (m k N : Nat) (hN : eulerCut N m k = false)
    (i : Nat) (hi : N ≤ i) : eulerCut i m k = false :=
  cut_false_fwd eAb m k N hN i hi

/-- The boundary case `m/k = e_{k+1}`: the cut is already `false` at `k+2`. -/
private theorem euler_eq_false_at_k2 (m k : Nat) (hk : 1 ≤ k)
    (heq : eulerNum (k+1) * k = eulerDen (k+1) * m) :
    eulerCut (k+2) m k = false := by
  rw [eulerCut_eq]; apply decide_eq_false
  have key : eulerNum (k+2) * k = eulerDen (k+2) * m + k := by
    show ((k+2)*eulerNum (k+1)+1)*k = (k+2)*eulerDen (k+1)*m + k
    rw [add_mul, Nat.one_mul, mul_assoc, heq, ← mul_assoc]
  intro hle
  rw [key] at hle
  exact absurd hle (Nat.not_le.mpr (Nat.lt_add_of_pos_right hk))

/-! ## §3 — the total modulus -/

/-- ★★★ **e has a total ∅-axiom cut modulus: `eulerCut` is constant past `k+2`.**
    For every `(m,k)` with `k ≥ 1`, `eulerCut i m k = eulerCut j m k` whenever
    `i, j ≥ k+2`.  Three decidable cases at index `k+1`: strict-below ⟹ true forever
    (`euler_inv`), equal ⟹ false from `k+2`, above ⟹ false from `k+1`.  So
    `N(m,k) = k+2` is an explicit total modulus — no LEM, no irrationality measure. -/
theorem euler_cut_const (m k : Nat) (hk : 1 ≤ k) (i j : Nat)
    (hi : k + 2 ≤ i) (hj : k + 2 ≤ j) : eulerCut i m k = eulerCut j m k := by
  have hk1i : k + 1 ≤ i := Nat.le_trans (Nat.le_succ _) hi
  have hk1j : k + 1 ≤ j := Nat.le_trans (Nat.le_succ _) hj
  rcases Nat.lt_trichotomy (eulerNum (k+1)*k) (eulerDen (k+1)*m) with hlt | heq | hgt
  · exact (euler_inv_cut m k i hk (euler_inv m k hlt i hk1i)).trans
        (euler_inv_cut m k j hk (euler_inv m k hlt j hk1j)).symm
  · have hf := euler_eq_false_at_k2 m k hk heq
    exact (euler_false_fwd m k (k+2) hf i hi).trans
        (euler_false_fwd m k (k+2) hf j hj).symm
  · have hfalse : eulerCut (k+1) m k = false := by
      rw [eulerCut_eq]; exact decide_eq_false (Nat.not_le.mpr hgt)
    exact (euler_false_fwd m k (k+1) hfalse i hk1i).trans
        (euler_false_fwd m k (k+1) hfalse j hk1j).symm

/-- ★★★ **The total modulus, existential form.**  For every `(m,k)` with `k ≥ 1`
    there is an `N` (namely `k+2`) past which e's convergent cut is constant — e's
    cut Cauchy property holds ∅-axiom at *every* `(m,k)`. -/
theorem euler_total_modulus (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → eulerCut i m k = eulerCut j m k :=
  ⟨k+2, fun i j hi hj => euler_cut_const m k hk i j hi hj⟩

/-! ## §4 — e as a `HolonomicReal` with a constructed total modulus -/

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.Real213.ExpLog.EulerCut (eulerCut_valid)

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
def eHolonomic : E213.Lib.Math.Real213.Holonomic where
  order := 1
  coeff := fun n => (n : Int) + 1
  cdeg  := fun _ => 1
  init  := fun _ => 1

/-- ★★★ **e is a complete `HolonomicReal`** — like φ, with the convergence modulus a
    *constructed field* (`eulerCauchySeq.N = k+2`), not a hypothesis.  The structured
    transcendental e inhabits the unconditional real API ∅-axiom: the general
    generator extends past the algebraic floor to (at least) the degree-1 holonomic
    class. -/
def eHolonomicReal : E213.Lib.Math.Real213.HolonomicReal where
  hol   := eHolonomic
  seq   := eulerCauchySeq
  valid := CauchyCutSeq.limit_valid eulerCauchySeq (fun i => eulerCut_valid i)

/-- ★★ **`eHolonomic` is the genuine recurrence, not decoration.**  e's convergent
    denominators and numerators satisfy the order-1 P-recursive recurrence whose
    coefficient is `eHolonomic.coeff n = (n:Int)+1` (degree 1): `eulerDen (n+1) =
    (n+1)·eulerDen n` and `eulerNum (n+1) = (n+1)·eulerNum n + 1`.  So
    `eHolonomicReal.hol` actually generates the cut-sequence `eHolonomicReal.seq` —
    the architecture's recurrence-to-data tie, discharged for e. -/
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
    exactly the (constant) tail value of the convergents, however far they are read.
    The e analogue of `phiHolonomicReal_cut`. -/
theorem eHolonomicReal_cut_stable (m k : Nat) (hk : 1 ≤ k) (i : Nat) (hi : k+2 ≤ i) :
    eHolonomicReal.cut m k = eulerCut i m k := by
  rw [eHolonomicReal_cut]; exact euler_cut_const m k hk (k+2) i (Nat.le_refl _) hi

/-! ## §5 — e satisfies the abstract rate certificate (the generator is non-vacuous) -/

open E213.Lib.Math.Real213.RateModulus (Htel rate_total_modulus Htel_of_crossdet)
open E213.Lib.Math.Cauchy.EulerDivergenceForm (euler_cross_det)

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
  intro i hi; rw [← E213.Tactic.NatHelper.add_sub_of_le hi]; exact aux (i - N)

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

/-- ★★★ **e's total modulus, derived from the abstract generator.**  Instantiating
    `RateModulus.rate_total_modulus` at e's convergents reproduces `euler_total_modulus`
    — the general "rate-carrying ⟹ total modulus" theorem applies to e, witnessing it
    is not vacuous. -/
theorem euler_total_modulus_via_rate (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → eulerCut i m k = eulerCut j m k := by
  obtain ⟨N, hN⟩ := rate_total_modulus eulerDen_pos euler_Htel euler_hmono euler_hmonoS m k hk
  exact ⟨N, fun i j hi hj => by
    rw [eulerCut_eq i m k, eulerCut_eq j m k]; exact hN i j hi hj⟩

end E213.Lib.Math.Real213.ExpLog.EulerModulus
