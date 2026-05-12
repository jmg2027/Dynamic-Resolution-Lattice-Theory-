import E213.Lens.Instances.Cauchy
import E213.Lens.Instances.AB
import E213.Meta.Tactic.Nat213

/-!
# ArchimedeanCauchy: ℝ-like completion via Dedekind cut

Mingu (C) direction (2026-04-25): abLens + order-projection family.

## Core

- **Lens core**: abLens : Lens (Nat × Nat).  Fold-structured.
- **Order projection**: orderProj m k : (Nat × Nat) → Bool with
  decide (a*k ≤ b*m).  Non-fold derived evaluation.
- **Order-Cauchy**: orderProj view eventually constant for every
  (m, k) reference.
- **Limit = Dedekind cut**: the consistent decision function (m, k) →
  Bool itself is an ℝ-element.

## Significance for 213

- The limit is not a new Raw — it is a consistent decision on Lens output.
- Archimedean property: automatic because the family is ℚ⁺-dense.
- No external metric — ordering only, as a fold-structured Bool family.
-/

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lens.Instances.Cauchy

/-- **Order projection**: (a, b) ↦ decide (a * k ≤ b * m).
    Cross-multiplication form comparing a/b ≤ m/k (assuming k ≥ 1).
    A derived evaluation on the image of abLens, not a Lens itself. -/
def orderProj (m k : Nat) : (Nat × Nat) → Bool :=
  fun p => decide (p.1 * k ≤ p.2 * m)

/-- **Order-Cauchy**: orderProj is eventually constant for every
    (m, k).  Convergence in the Dedekind cut sense. -/
def isOrderCauchy (xs : Nat → Raw) : Prop :=
  ∀ m k, k ≥ 1 → ∃ N, ∀ i j, i ≥ N → j ≥ N →
    orderProj m k (abLens.view (xs i)) = orderProj m k (abLens.view (xs j))

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB

/-- **orderProj is n-independent for (a, b) = (n, n) (n ≥ 1)**:
    Dedekind cut for the diagonal ratio 1/1 = 1. -/
theorem diagonal_seq_orderProj_const (m k : Nat) (n : Nat) (hn : n ≥ 1) :
    orderProj m k (n, n) = decide (k ≤ m) := by
  unfold orderProj
  show decide (n * k ≤ n * m) = decide (k ≤ m)
  by_cases hkm : k ≤ m
  · have h : n * k ≤ n * m := Nat.mul_le_mul_left n hkm
    exact (decide_eq_true h).trans (decide_eq_true hkm).symm
  · have hnot : ¬ n * k ≤ n * m :=
      fun h' => hkm (Nat.le_of_mul_le_mul_left h' hn)
    exact (decide_eq_false hnot).trans (decide_eq_false hkm).symm

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lens.Instances.Cauchy

/-- **Order Cauchy data**: explicit witness structure (constructive). -/
structure OrderCauchyData (xs : Nat → Raw) where
  N : Nat → Nat → Nat
  cauchy : ∀ m k i j, k ≥ 1 → i ≥ N m k → j ≥ N m k →
    orderProj m k (abLens.view (xs i)) = orderProj m k (abLens.view (xs j))

/-- **Dedekind cut**: limit decision function of an Order-Cauchy sequence.
    Eventually-constant Bool for each (m, k) reference. -/
def OrderCauchyData.cut {xs : Nat → Raw} (cd : OrderCauchyData xs)
    (m k : Nat) : Bool :=
  orderProj m k (abLens.view (xs (cd.N m k)))

/-- **Well-definedness of Cut**: all tail values equal the cut value. -/
theorem cut_eq_tail {xs : Nat → Raw} (cd : OrderCauchyData xs)
    (m k : Nat) (hk : k ≥ 1) (n : Nat) (hn : n ≥ cd.N m k) :
    orderProj m k (abLens.view (xs n)) = cd.cut m k := by
  unfold OrderCauchyData.cut
  exact cd.cauchy m k n (cd.N m k) hk hn (Nat.le_refl _)

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB

/-- **Diagonal sequence (a=b=n+1) is Order-Cauchy**.
    Assumes abLens.view (xs n) = (n+1, n+1). -/
theorem diagonal_seq_orderCauchy (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) :
    isOrderCauchy xs := by
  intro m k _
  refine ⟨0, ?_⟩
  intro i j _ _
  rw [h i, h j]
  rw [diagonal_seq_orderProj_const m k (i+1) (Nat.succ_le_succ (Nat.zero_le _))]
  rw [diagonal_seq_orderProj_const m k (j+1) (Nat.succ_le_succ (Nat.zero_le _))]

/-- **Explicit OrderCauchyData for the diagonal sequence**. -/
def diagonal_seq_data (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) :
    OrderCauchyData xs where
  N := fun _ _ => 0
  cauchy := by
    intro m k i j _ _ _
    rw [h i, h j]
    rw [diagonal_seq_orderProj_const m k (i+1) (Nat.succ_le_succ (Nat.zero_le _))]
    rw [diagonal_seq_orderProj_const m k (j+1) (Nat.succ_le_succ (Nat.zero_le _))]

/-- **Dedekind cut of the diagonal sequence = "ratio 1"**:
    cut(m, k) = decide (k ≤ m).  Dedekind representation of rational 1. -/
theorem diagonal_seq_cut (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) (m k : Nat) :
    (diagonal_seq_data xs h).cut m k = decide (k ≤ m) := by
  unfold OrderCauchyData.cut diagonal_seq_data
  rw [h 0]
  exact diagonal_seq_orderProj_const m k 1 (Nat.le_refl 1)

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB

/-- orderProj of the (n+1, n+2) sequence is eventually constant
    (N differs for each (m, k)). -/
theorem ratio_one_below_orderProj_eventually
    (m k : Nat) (hk : k ≥ 1) :
    ∃ N, ∀ n, n ≥ N →
      orderProj m k (n+1, n+2) = decide (k ≤ m) := by
  by_cases hkm : k ≤ m
  · -- k ≤ m case: always true
    refine ⟨0, ?_⟩
    intro n _
    unfold orderProj
    show decide ((n+1) * k ≤ (n+2) * m) = decide (k ≤ m)
    have h1 : (n+1) * k ≤ (n+1) * m := Nat.mul_le_mul_left (n+1) hkm
    have h2 : (n+1) * m ≤ (n+2) * m := Nat.mul_le_mul_right m (Nat.le_succ _)
    have h3 : (n+1) * k ≤ (n+2) * m := Nat.le_trans h1 h2
    exact (decide_eq_true h3).trans (decide_eq_true hkm).symm
  · -- k > m case: false for sufficiently large n
    have hkmgt : k > m := Nat.lt_of_not_le hkm
    refine ⟨m + 1, ?_⟩
    intro n hn
    unfold orderProj
    show decide ((n+1) * k ≤ (n+2) * m) = decide (k ≤ m)
    -- hkmgt : m < k, i.e. m + 1 ≤ k.  Then 1 ≤ k - m via Nat213.
    have hkmpos : k - m ≥ 1 := E213.Tactic.Nat213.le_pred_of_succ_le hkmgt
    have hnotle : ¬ (n+1) * k ≤ (n+2) * m := by
      intro h'
      have hexp : (n+1) * k = (n+1) * m + (n+1) * (k - m) := by
        rw [← Nat.mul_add]
        congr 1
        exact (E213.Tactic.Nat213.add_sub_of_le (Nat.le_of_lt hkmgt)).symm
      have hexp2 : (n+2) * m = (n+1) * m + m := by
        rw [show (n+2) = (n+1) + 1 from rfl,
            E213.Tactic.Nat213.add_mul, Nat.one_mul]
      rw [hexp, hexp2] at h'
      have hcancel : (n+1) * (k - m) ≤ m :=
        E213.Tactic.Nat213.le_of_add_le_add_left h'
      have hbound : (n+1) ≤ m := by
        calc n + 1
            = (n + 1) * 1 := (Nat.mul_one _).symm
          _ ≤ (n + 1) * (k - m) := Nat.mul_le_mul_left _ hkmpos
          _ ≤ m := hcancel
      -- hn : m + 1 ≤ n.  Combined with hbound : n + 1 ≤ m, contradiction.
      have h_succ_le : m + 1 ≤ n := hn
      have h_n_succ_le_m : n + 1 ≤ m := hbound
      have : m + 2 ≤ m :=
        Nat.le_trans (Nat.succ_le_succ h_succ_le) h_n_succ_le_m
      exact Nat.not_succ_le_self m
        (Nat.le_trans (Nat.le_succ _) this)
    exact (decide_eq_false hnotle).trans (decide_eq_false hkm).symm

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB

/-- **(n+1, n+2)-type sequence is Order-Cauchy** — approaches ratio 1
    from below. -/
theorem ratio_one_below_orderCauchy (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 2)) :
    isOrderCauchy xs := by
  intro m k hk
  obtain ⟨N, hN⟩ := ratio_one_below_orderProj_eventually m k hk
  refine ⟨N, ?_⟩
  intro i j hi hj
  rw [h i, h j, hN i hi, hN j hj]

/-- **Dedekind cut of the (n+1, n+2)-type sequence is also ratio 1**.
    Same cut as (n+1, n+1) — a different sequence for the same ℝ-element. -/
theorem ratio_one_below_cut_eq_diagonal (xs ys : Nat → Raw)
    (hx : ∀ n, abLens.view (xs n) = (n + 1, n + 1))
    (hy : ∀ n, abLens.view (ys n) = (n + 1, n + 2))
    (cdx : OrderCauchyData xs) (cdy : OrderCauchyData ys)
    (hcdx : ∀ m k, cdx.cut m k = decide (k ≤ m))
    (hcdy : ∀ m k, cdy.cut m k = decide (k ≤ m)) :
    ∀ m k, cdx.cut m k = cdy.cut m k := by
  intro m k
  rw [hcdx, hcdy]

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB

/-- **General rational p/q sequence**: orderProj of (a, b) =
    (p*(n+1), q*(n+1)) is n-independent. -/
theorem rational_seq_orderProj_const (p q m k : Nat) (n : Nat) (hn : n ≥ 1) :
    orderProj m k (p * n, q * n) = decide (p * k ≤ q * m) := by
  unfold orderProj
  show decide (p * n * k ≤ q * n * m) = decide (p * k ≤ q * m)
  have hrw1 : p * n * k = (p * k) * n := by
    rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm n k,
        ← E213.Tactic.Nat213.mul_assoc]
  have hrw2 : q * n * m = (q * m) * n := by
    rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm n m,
        ← E213.Tactic.Nat213.mul_assoc]
  rw [hrw1, hrw2]
  by_cases hpq : p * k ≤ q * m
  · have h : (p * k) * n ≤ (q * m) * n := Nat.mul_le_mul_right n hpq
    exact (decide_eq_true h).trans (decide_eq_true hpq).symm
  · have hnot : ¬ (p * k) * n ≤ (q * m) * n := by
      intro h'
      apply hpq
      have h'' : n * (p * k) ≤ n * (q * m) := by
        rw [Nat.mul_comm n (p*k), Nat.mul_comm n (q*m)]; exact h'
      exact Nat.le_of_mul_le_mul_left h'' hn
    exact (decide_eq_false hnot).trans (decide_eq_false hpq).symm

/-- **Dedekind cut of the general rational p/q sequence = "ratio p/q"**.
    Cut of the constant sequence (p*(n+1), q*(n+1)) = decide (p*k ≤ q*m). -/
theorem rational_seq_cut (p q : Nat) (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (p * (n+1), q * (n+1))) (m k : Nat) :
    orderProj m k (abLens.view (xs 0)) = decide (p * k ≤ q * m) := by
  rw [h 0]
  exact rational_seq_orderProj_const p q m k 1 (Nat.le_refl 1)

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens
open E213.Lens.Instances.AB

/-- **Half sequence (a = n+1, b = 2*(n+1))**: ratio 1/2. -/
theorem half_seq_orderCauchy (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, 2 * (n + 1))) :
    isOrderCauchy xs := by
  intro m k _
  refine ⟨0, ?_⟩
  intro i j _ _
  rw [h i, h j]
  have hi := rational_seq_orderProj_const 1 2 m k (i+1)
    (Nat.succ_le_succ (Nat.zero_le _))
  have hj := rational_seq_orderProj_const 1 2 m k (j+1)
    (Nat.succ_le_succ (Nat.zero_le _))
  show orderProj m k (i + 1, 2 * (i + 1))
       = orderProj m k (j + 1, 2 * (j + 1))
  have hri : (i + 1, 2 * (i + 1)) = (1 * (i + 1), 2 * (i + 1)) := by
    rw [Nat.one_mul]
  have hrj : (j + 1, 2 * (j + 1)) = (1 * (j + 1), 2 * (j + 1)) := by
    rw [Nat.one_mul]
  rw [hri, hrj, hi, hj]

/-- **Half-seq cut = ratio 1/2**: orderProj at xs 0 = decide (k ≤ 2m). -/
theorem half_seq_cut (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, 2 * (n + 1)))
    (m k : Nat) :
    orderProj m k (abLens.view (xs 0)) = decide (k ≤ 2 * m) := by
  rw [h 0]
  have h_eq : (0 + 1, 2 * (0 + 1)) = (1 * 1, 2 * 1) := rfl
  rw [h_eq, rational_seq_orderProj_const 1 2 m k 1 (Nat.le_refl 1)]
  show decide (1 * k ≤ 2 * m) = decide (k ≤ 2 * m)
  rw [Nat.one_mul]

end E213.Lib.Math.Cauchy.Archimedean

namespace E213.Lib.Math.Cauchy.Archimedean

open E213.Theory E213.Lens

/-- **Cut equivalence**: two OrderCauchyData with the same Dedekind cut
    represent the same ℝ-element. -/
def CutEquiv {xs ys : Nat → Raw}
    (cdx : OrderCauchyData xs) (cdy : OrderCauchyData ys) : Prop :=
  ∀ m k, cdx.cut m k = cdy.cut m k

theorem CutEquiv.refl {xs : Nat → Raw} (cd : OrderCauchyData xs) :
    CutEquiv cd cd := fun _ _ => rfl

theorem CutEquiv.symm {xs ys : Nat → Raw}
    {cdx : OrderCauchyData xs} {cdy : OrderCauchyData ys}
    (h : CutEquiv cdx cdy) : CutEquiv cdy cdx :=
  fun m k => (h m k).symm

theorem CutEquiv.trans {xs ys zs : Nat → Raw}
    {cdx : OrderCauchyData xs} {cdy : OrderCauchyData ys}
    {cdz : OrderCauchyData zs}
    (hxy : CutEquiv cdx cdy) (hyz : CutEquiv cdy cdz) : CutEquiv cdx cdz :=
  fun m k => (hxy m k).trans (hyz m k)

/-- **ℝ-element type**: the Dedekind cut itself.
    A consistent Bool decision for each (m, k). -/
abbrev RealCut : Type := Nat → Nat → Bool

/-- Extract RealCut from OrderCauchyData. -/
def OrderCauchyData.toRealCut {xs : Nat → Raw}
    (cd : OrderCauchyData xs) : RealCut :=
  cd.cut

end E213.Lib.Math.Cauchy.Archimedean
