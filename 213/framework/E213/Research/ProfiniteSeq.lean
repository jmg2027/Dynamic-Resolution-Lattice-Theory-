import E213.Research.LensCauchy
import E213.Research.LeavesModNat
import E213.Infinity.LensCardinality

/-!
# Research.ProfiniteSeq: leavesModNat family 의 Cauchy instance

Mingu 제안 (b): leavesModNat family 의 specific Cauchy seq 가
**profinite ℤ̂ (= Ẑ) 와 유사한 구조** 생성 함의 형식 demonstration.

## 핵심

leaves(xs n) = factorial(n+1) 인 sequence xs 는 family-Cauchy
w.r.t. {leavesModNat m : m ≥ 2}.

각 m ≥ 2 에 대해, n+1 ≥ m → factorial(n+1) ≡ 0 (mod m).
따라서 limit class = "0 mod m for all m" = profinite zero.

직관 적으로 ℕ 의 "무한대" 에 해당 — Ẑ-style 의 profinite 0.

## 의의

213 framework 가 단지 finite combinatorics 에 머무르지 않고
**profinite (algebraic) limit** 도 자연스럽게 생성.

leavesModNat family 의 iProdLens 가 정확히 ℤ̂-like profinite
완비화.  Lens-as-completion 의 구체 instance.
-/

namespace E213.Research.ProfiniteSeq

open E213.Firmware E213.Hypervisor
open E213.Research.LensCauchy

/-- Local factorial (Lean 4 core 에는 없음). -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

theorem factorial_pos (n : Nat) : factorial n ≥ 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      show (k+1) * factorial k ≥ 1
      have := Nat.mul_le_mul_left (k+1) ih
      simp at this
      omega

/-- factorial n 이 모든 m ≤ n 으로 나누어짐. -/
theorem factorial_dvd (m n : Nat) (h : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ factorial n := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hkm : m ≤ k
      · have hdvd : m ∣ factorial k := ih hkm
        show m ∣ (k+1) * factorial k
        obtain ⟨q, hq⟩ := hdvd
        refine ⟨(k+1) * q, ?_⟩
        calc (k + 1) * factorial k = (k + 1) * (m * q) := by rw [hq]
          _ = m * ((k + 1) * q) := by
              rw [← Nat.mul_assoc]
              rw [Nat.mul_comm (k + 1) m]
              rw [Nat.mul_assoc]
      · have hmk1 : m = k + 1 := by omega
        show m ∣ (k+1) * factorial k
        rw [hmk1]
        exact ⟨factorial k, rfl⟩

end E213.Research.ProfiniteSeq

namespace E213.Research.ProfiniteSeq

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat E213.Research.LensCauchy

/-- factorial seq 가 mod m 으로 eventually 0 (n + 1 ≥ m 이면). -/
theorem factorial_eventually_zero_mod (m : Nat) (hm : 1 ≤ m)
    (n : Nat) (hn : n + 1 ≥ m) : factorial (n + 1) % m = 0 := by
  obtain ⟨q, hq⟩ := factorial_dvd m (n + 1) hm hn
  rw [hq, Nat.mul_mod_right]

/-- **Cauchy w.r.t. leavesModNat m**: factorial-leaves seq 는
    각 m ≥ 2 에 대해 leavesModNat m Cauchy. -/
theorem factorial_seq_cauchy (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    LensCauchy (leavesModNat m) xs := by
  refine ⟨m, ?_⟩
  intro k l hk hl
  show (leavesModNat m).view (xs k) = (leavesModNat m).view (xs l)
  rw [leavesModNat_view_eq, leavesModNat_view_eq]
  rw [hLeaves k, hLeaves l]
  rw [factorial_eventually_zero_mod m (by omega) k (by omega)]
  rw [factorial_eventually_zero_mod m (by omega) l (by omega)]

/-- **Profinite limit**: factorial-leaves seq 의 leavesModNat m
    limit 이 0.  Ẑ 의 profinite zero 와 정확히 대응. -/
theorem factorial_seq_limit_zero (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    EventuallyClass (leavesModNat m) xs 0 := by
  refine ⟨m, ?_⟩
  intro n hn
  show (leavesModNat m).view (xs n) = 0
  rw [leavesModNat_view_eq, hLeaves n]
  exact factorial_eventually_zero_mod m (by omega) n (by omega)

/-- **Family Cauchy** w.r.t. leavesModNat family ({m : m ≥ 2}). -/
def leavesModNatFamily : { m : Nat // m ≥ 2 } → (α : Type) × Lens α :=
  fun m => ⟨Nat, leavesModNat m.val⟩

/-- factorial-leaves seq 가 leavesModNat family 전체 에 대해
    family-Cauchy.  Profinite Cauchy 의 형식 표현. -/
theorem factorial_seq_familyCauchy (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1)) :
    FamilyCauchy leavesModNatFamily xs := by
  intro ⟨m, hm⟩
  exact factorial_seq_cauchy xs hLeaves m hm

/-- **Profinite limit assignment**: factorial seq 의 family-Cauchy
    limit 이 모든 m 에 대해 0.  Ẑ 의 0 element 의 213 표현. -/
theorem factorial_seq_limit_all_zero (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (la : LimitAssignment leavesModNatFamily xs)
    (m : Nat) (hm : m ≥ 2) :
    la.limit ⟨m, hm⟩ = (0 : Nat) := by
  have h0 : EventuallyClass (leavesModNat m) xs 0 :=
    factorial_seq_limit_zero xs hLeaves m hm
  have hL : EventuallyClass (leavesModNat m) xs (la.limit ⟨m, hm⟩) := by
    refine ⟨(la.data ⟨m, hm⟩).N, ?_⟩
    intro n hn
    exact limitClass_eq_tail (leavesModNat m) xs (la.data ⟨m, hm⟩) n hn
  exact eventually_class_unique (leavesModNat m) xs (la.limit ⟨m, hm⟩) 0 hL h0

end E213.Research.ProfiniteSeq
