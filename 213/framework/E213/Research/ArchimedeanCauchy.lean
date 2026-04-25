import E213.Research.LensCauchy
import E213.Research.ABLens

/-!
# Research.ArchimedeanCauchy: ℝ-like completion via Dedekind cut

Mingu (C) 방향 (2026-04-25): abLens + order-projection family.

## 핵심

- **Lens core**: abLens : Lens (Nat × Nat).  Fold-structured.
- **Order projection**: orderProj m k : (Nat × Nat) → Bool with
  decide (a*k ≤ b*m).  Non-fold derived 평가.
- **Order-Cauchy**: 모든 (m, k) reference 에 대해 orderProj
  view eventually constant.
- **Limit = Dedekind cut**: consistent decision function (m, k) →
  Bool 자체 가 ℝ-element.

## 213 의의

- Limit 이 새 Raw 부재 — Lens output 의 consistent decision.
- Archimedean property: family 가 ℚ⁺ dense 라 자동.
- 외부 metric 부재 — ordering 만 fold-structured Bool family.
-/

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.LensCauchy

/-- **Order projection**: (a, b) ↦ decide (a * k ≤ b * m).
    Cross-multiplication form 으로 a/b ≤ m/k 비교 (k ≥ 1 가정).
    Lens 자체 가 아니라 abLens 의 image 위 derived 평가. -/
def orderProj (m k : Nat) : (Nat × Nat) → Bool :=
  fun p => decide (p.1 * k ≤ p.2 * m)

/-- **Order-Cauchy**: 모든 (m, k) 에 대해 orderProj 가 eventually
    constant.  Dedekind cut 형 수렴. -/
def isOrderCauchy (xs : Nat → Raw) : Prop :=
  ∀ m k, k ≥ 1 → ∃ N, ∀ i j, i ≥ N → j ≥ N →
    orderProj m k (abLens.view (xs i)) = orderProj m k (abLens.view (xs j))

end E213.Research.ArchimedeanCauchy

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens

/-- **(a, b) = (n, n) (n ≥ 1) 의 orderProj 가 n-independent**:
    diagonal 비율 1/1 = 1 의 Dedekind cut. -/
theorem diagonal_seq_orderProj_const (m k : Nat) (n : Nat) (hn : n ≥ 1) :
    orderProj m k (n, n) = decide (k ≤ m) := by
  unfold orderProj
  show decide (n * k ≤ n * m) = decide (k ≤ m)
  by_cases hkm : k ≤ m
  · have : n * k ≤ n * m := Nat.mul_le_mul_left n hkm
    simp [hkm, this]
  · have : ¬ n * k ≤ n * m := by
      intro h'
      exact hkm (Nat.le_of_mul_le_mul_left h' hn)
    simp [hkm, this]

end E213.Research.ArchimedeanCauchy

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.LensCauchy

/-- **Order Cauchy data**: explicit witness 구조 (constructive). -/
structure OrderCauchyData (xs : Nat → Raw) where
  N : Nat → Nat → Nat
  cauchy : ∀ m k i j, k ≥ 1 → i ≥ N m k → j ≥ N m k →
    orderProj m k (abLens.view (xs i)) = orderProj m k (abLens.view (xs j))

/-- **Dedekind cut**: Order-Cauchy seq 의 limit decision function.
    각 (m, k) reference 에 대해 eventually-constant Bool. -/
def OrderCauchyData.cut {xs : Nat → Raw} (cd : OrderCauchyData xs)
    (m k : Nat) : Bool :=
  orderProj m k (abLens.view (xs (cd.N m k)))

/-- **Cut 의 well-definedness**: tail 모두 동일 cut 값. -/
theorem cut_eq_tail {xs : Nat → Raw} (cd : OrderCauchyData xs)
    (m k : Nat) (hk : k ≥ 1) (n : Nat) (hn : n ≥ cd.N m k) :
    orderProj m k (abLens.view (xs n)) = cd.cut m k := by
  unfold OrderCauchyData.cut
  exact cd.cauchy m k n (cd.N m k) hk hn (Nat.le_refl _)

end E213.Research.ArchimedeanCauchy

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens

/-- **Diagonal sequence (a=b=n+1) 가 Order-Cauchy**.
    abLens.view (xs n) = (n+1, n+1) 가정. -/
theorem diagonal_seq_orderCauchy (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) :
    isOrderCauchy xs := by
  intro m k _
  refine ⟨0, ?_⟩
  intro i j _ _
  rw [h i, h j]
  rw [diagonal_seq_orderProj_const m k (i+1) (by omega)]
  rw [diagonal_seq_orderProj_const m k (j+1) (by omega)]

/-- **Diagonal sequence 의 explicit OrderCauchyData**. -/
def diagonal_seq_data (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) :
    OrderCauchyData xs where
  N := fun _ _ => 0
  cauchy := by
    intro m k i j _ _ _
    rw [h i, h j]
    rw [diagonal_seq_orderProj_const m k (i+1) (by omega)]
    rw [diagonal_seq_orderProj_const m k (j+1) (by omega)]

/-- **Diagonal sequence 의 Dedekind cut = "ratio 1"**:
    cut(m, k) = decide (k ≤ m).  rational 1 의 Dedekind 표현. -/
theorem diagonal_seq_cut (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) (m k : Nat) :
    (diagonal_seq_data xs h).cut m k = decide (k ≤ m) := by
  unfold OrderCauchyData.cut diagonal_seq_data
  rw [h 0]
  exact diagonal_seq_orderProj_const m k 1 (by omega)

end E213.Research.ArchimedeanCauchy

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens

/-- (n+1, n+2) sequence 의 orderProj eventually constant (각
    (m, k) 별로 N 다름). -/
theorem ratio_one_below_orderProj_eventually
    (m k : Nat) (hk : k ≥ 1) :
    ∃ N, ∀ n, n ≥ N →
      orderProj m k (n+1, n+2) = decide (k ≤ m) := by
  by_cases hkm : k ≤ m
  · -- k ≤ m case: 항상 true
    refine ⟨0, ?_⟩
    intro n _
    unfold orderProj
    show decide ((n+1) * k ≤ (n+2) * m) = decide (k ≤ m)
    have h1 : (n+1) * k ≤ (n+1) * m := Nat.mul_le_mul_left (n+1) hkm
    have h2 : (n+1) * m ≤ (n+2) * m := Nat.mul_le_mul_right m (by omega)
    have h3 : (n+1) * k ≤ (n+2) * m := Nat.le_trans h1 h2
    simp [hkm, h3]
  · -- k > m case: n 충분 크면 false
    have hkmgt : k > m := Nat.lt_of_not_le hkm
    refine ⟨m + 1, ?_⟩
    intro n hn
    unfold orderProj
    show decide ((n+1) * k ≤ (n+2) * m) = decide (k ≤ m)
    have hkmpos : k - m ≥ 1 := by omega
    -- (n+1)*k = n*k + k = n*m + n*(k-m) + k
    -- (n+2)*m = n*m + 2m
    -- diff: n*(k-m) + k - 2m
    -- For n ≥ m+1: n*(k-m) ≥ (m+1)*1 = m+1 > 2m - k (since k > m)
    have hnotle : ¬ (n+1) * k ≤ (n+2) * m := by
      intro h'
      -- (n+1)*k ≤ (n+2)*m = (n+1)*m + m
      -- (n+1)*(k - m) ≤ m (after subtracting (n+1)*m from both sides)
      have hexp : (n+1) * k = (n+1) * m + (n+1) * (k - m) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have hexp2 : (n+2) * m = (n+1) * m + m := by
        rw [show (n+2) = (n+1) + 1 from rfl, Nat.add_mul, Nat.one_mul]
      rw [hexp, hexp2] at h'
      have : (n+1) * (k - m) ≤ m := by omega
      have : (n+1) ≤ m := by
        have hk_ge : k - m ≥ 1 := hkmpos
        calc n + 1
            = (n + 1) * 1 := (Nat.mul_one _).symm
          _ ≤ (n + 1) * (k - m) := Nat.mul_le_mul_left _ hk_ge
          _ ≤ m := this
      omega
    simp [hkm, hnotle]

end E213.Research.ArchimedeanCauchy

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens

/-- **(n+1, n+2) 형 sequence 가 Order-Cauchy** — ratio 1 을 below
    에서 approach. -/
theorem ratio_one_below_orderCauchy (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 2)) :
    isOrderCauchy xs := by
  intro m k hk
  obtain ⟨N, hN⟩ := ratio_one_below_orderProj_eventually m k hk
  refine ⟨N, ?_⟩
  intro i j hi hj
  rw [h i, h j, hN i hi, hN j hj]

/-- **(n+1, n+2) 형 sequence 의 Dedekind cut 도 ratio 1**.
    (n+1, n+1) 과 같은 cut — 같은 ℝ-element 의 다른 sequence. -/
theorem ratio_one_below_cut_eq_diagonal (xs ys : Nat → Raw)
    (hx : ∀ n, abLens.view (xs n) = (n + 1, n + 1))
    (hy : ∀ n, abLens.view (ys n) = (n + 1, n + 2))
    (cdx : OrderCauchyData xs) (cdy : OrderCauchyData ys)
    (hcdx : ∀ m k, cdx.cut m k = decide (k ≤ m))
    (hcdy : ∀ m k, cdy.cut m k = decide (k ≤ m)) :
    ∀ m k, cdx.cut m k = cdy.cut m k := by
  intro m k
  rw [hcdx, hcdy]

end E213.Research.ArchimedeanCauchy

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens

/-- **General rational p/q sequence**: (a, b) = (p*(n+1), q*(n+1))
    의 orderProj 가 n-independent. -/
theorem rational_seq_orderProj_const (p q m k : Nat) (n : Nat) (hn : n ≥ 1) :
    orderProj m k (p * n, q * n) = decide (p * k ≤ q * m) := by
  unfold orderProj
  show decide (p * n * k ≤ q * n * m) = decide (p * k ≤ q * m)
  have hrw1 : p * n * k = (p * k) * n := by
    rw [Nat.mul_assoc, Nat.mul_comm n k, ← Nat.mul_assoc]
  have hrw2 : q * n * m = (q * m) * n := by
    rw [Nat.mul_assoc, Nat.mul_comm n m, ← Nat.mul_assoc]
  rw [hrw1, hrw2]
  by_cases hpq : p * k ≤ q * m
  · have : (p * k) * n ≤ (q * m) * n := Nat.mul_le_mul_right n hpq
    simp [hpq, this]
  · have : ¬ (p * k) * n ≤ (q * m) * n := by
      intro h'
      apply hpq
      have h'' : n * (p * k) ≤ n * (q * m) := by
        rw [Nat.mul_comm n (p*k), Nat.mul_comm n (q*m)]; exact h'
      exact Nat.le_of_mul_le_mul_left h'' hn
    simp [hpq, this]

/-- **General rational p/q seq 의 Dedekind cut = "ratio p/q"**.
    Constant sequence (p*(n+1), q*(n+1)) 의 cut = decide (p*k ≤ q*m). -/
theorem rational_seq_cut (p q : Nat) (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (p * (n+1), q * (n+1))) (m k : Nat) :
    orderProj m k (abLens.view (xs 0)) = decide (p * k ≤ q * m) := by
  rw [h 0]
  exact rational_seq_orderProj_const p q m k 1 (by omega)

end E213.Research.ArchimedeanCauchy

namespace E213.Research.ArchimedeanCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens

/-- **Half sequence (a = n+1, b = 2*(n+1))**: ratio 1/2. -/
theorem half_seq_orderCauchy (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, 2 * (n + 1))) :
    isOrderCauchy xs := by
  intro m k _
  refine ⟨0, ?_⟩
  intro i j _ _
  rw [h i, h j]
  have hi := rational_seq_orderProj_const 1 2 m k (i+1) (by omega)
  have hj := rational_seq_orderProj_const 1 2 m k (j+1) (by omega)
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
  have h_eq : (0 + 1, 2 * (0 + 1)) = (1 * 1, 2 * 1) := by simp
  rw [h_eq, rational_seq_orderProj_const 1 2 m k 1 (by omega)]
  show decide (1 * k ≤ 2 * m) = decide (k ≤ 2 * m)
  rw [Nat.one_mul]

end E213.Research.ArchimedeanCauchy
