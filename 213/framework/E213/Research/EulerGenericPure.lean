import E213.Research.PureNat
import E213.Research.EulerSeq

/-!
# Research.EulerGenericPure: Generic Euler lower bound (meta-algorithm)

User insight: 임의 b 에 대 한 sharper Euler bound 를 *parameterized*
template 으 로.  per-b 의 manual 작업 → *single generic theorem* +
per-b base case `decide`.

## 구 성

`euler_lower_generic`: ∀ j b (hb : b ≥ 1), N0 base case 만 주어
지 면, ∀ n ≥ N0, b·eulerNum n ≥ j·eulerDen n + 1.

Inductive step: IH × (k+1) + arithmetic chain.  계 수 (b, j) 에
무관 — pattern *mechanical generic*.

## 의 의

User 의 깊은 통찰: "각 b 에 대 한 sharper bound 의 메타 알고리즘".
이게 그 구 현 — single generic theorem 으 로 모든 b 의 lower
bound 가 즉시 유도.  per-b application 은 base case `decide` 만.

각 b 의 (j, b) pair 가 e ∈ (j/b, (j+1)/b) 의 sharp interval 결정.
upper bound 는 별 도 (`euler_upper_pure` 의 generic version 도
가능).

## 현재 status

- Generic lower theorem 완료.
- Per-b application: b=3 (j=8), b=5 (j=13) 등 demonstrated.
- 모두 axiom budget = `[propext]` 만 (Quot.sound 부재).
-/

namespace E213.Research.EulerGenericPure

open E213.Research.PureNat
open E213.Research.EulerSeq

/-- **Inductive step lemma**: IH `b · a_k ≥ j · d_k + 1` →
    `b · a_{k+1} ≥ j · d_{k+1} + 1`.

    Pure arithmetic chain, no omega. -/
theorem euler_lower_step (j b k : Nat) (hb : b ≥ 1)
    (h_inv : b * eulerNum k ≥ j * eulerDen k + 1) :
    b * eulerNum (k + 1) ≥ j * eulerDen (k + 1) + 1 := by
  show b * ((k + 1) * eulerNum k + 1) ≥ j * ((k + 1) * eulerDen k) + 1
  -- LHS = (k+1) * (b * eulerNum k) + b
  -- RHS = (k+1) * (j * eulerDen k) + 1
  have h_lhs : b * ((k+1) * eulerNum k + 1) = (k+1) * (b * eulerNum k) + b := by
    rw [Nat.mul_add, Nat.mul_one, ← mul_assoc, Nat.mul_comm b (k+1), mul_assoc]
  have h_rhs : j * ((k+1) * eulerDen k) = (k+1) * (j * eulerDen k) := by
    rw [← mul_assoc, Nat.mul_comm j (k+1), mul_assoc]
  rw [h_lhs, h_rhs]
  have h_mul : (k+1) * (b * eulerNum k) ≥ (k+1) * (j * eulerDen k + 1) :=
    Nat.mul_le_mul_left (k+1) h_inv
  have h_dist : (k+1) * (j * eulerDen k + 1)
              = (k+1) * (j * eulerDen k) + (k+1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [h_dist] at h_mul
  -- h_mul : (k+1) * (b * eulerNum k) ≥ (k+1) * (j * eulerDen k) + (k+1)
  -- Need: (k+1) * (b * eulerNum k) + b ≥ (k+1) * (j * eulerDen k) + 1
  have h_add_b : (k+1) * (b * eulerNum k) + b ≥
                 (k+1) * (j * eulerDen k) + (k+1) + b :=
    Nat.add_le_add_right h_mul b
  have h_drop : (k+1) * (j * eulerDen k) + (k+1) + b ≥
                (k+1) * (j * eulerDen k) + 1 := by
    rw [Nat.add_assoc]
    apply Nat.add_le_add_left
    -- (k+1) + b ≥ 1 (since both ≥ 1)
    have : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact Nat.le_trans this (Nat.le_add_right (k+1) b)
  exact Nat.le_trans h_drop h_add_b

/-- **Generic Euler lower bound (META-ALGORITHM)**: ∀ j b (b ≥ 1)
    N0, base case verification 만 주어 지 면 ∀ n ≥ N0,
    `b · eulerNum n ≥ j · eulerDen n + 1` (== S_n > j/b strict).

    인 자: per-(j, b) 의 base case 만 `decide` 로 verify. -/
theorem euler_lower_generic (j b N0 : Nat) (hb : b ≥ 1)
    (h_base : b * eulerNum N0 ≥ j * eulerDen N0 + 1) :
    ∀ n, n ≥ N0 → b * eulerNum n ≥ j * eulerDen n + 1 := by
  intro n hn
  -- Induction on (n - N0) via auxiliary form.
  induction n with
  | zero =>
      have hN0 : N0 = 0 := Nat.le_zero.mp hn
      rw [hN0] at h_base
      exact h_base
  | succ k ih =>
      rcases Nat.lt_or_ge k N0 with h_lt | h_ge
      · -- k < N0, so k + 1 = N0 (since k + 1 ≥ N0)
        have h_kp1 : k + 1 = N0 := by
          have h1 : N0 ≤ k + 1 := hn
          have h2 : k + 1 ≤ N0 := h_lt
          exact Nat.le_antisymm h2 h1
        rw [h_kp1]
        exact h_base
      · have h_inv := ih h_ge
        exact euler_lower_step j b k hb h_inv

/-! ### Per-b applications via meta-algorithm -/

/-- e > 8/3 strict (b=3, j=8, N0=4). -/
theorem e_gt_8_3 (n : Nat) (hn : n ≥ 4) :
    3 * eulerNum n ≥ 8 * eulerDen n + 1 :=
  euler_lower_generic 8 3 4 (by decide) (by decide) n hn

/-- e > 10/4 = 5/2 strict (b=4, j=10, N0=4). -/
theorem e_gt_10_4 (n : Nat) (hn : n ≥ 4) :
    4 * eulerNum n ≥ 10 * eulerDen n + 1 :=
  euler_lower_generic 10 4 4 (by decide) (by decide) n hn

/-- e > 13/5 strict (b=5, j=13, N0=5). -/
theorem e_gt_13_5 (n : Nat) (hn : n ≥ 5) :
    5 * eulerNum n ≥ 13 * eulerDen n + 1 :=
  euler_lower_generic 13 5 5 (by decide) (by decide) n hn

/-- e > 19/7 strict (b=7, j=19, N0=6).  e ≈ 2.718, 19/7 ≈ 2.714. -/
theorem e_gt_19_7 (n : Nat) (hn : n ≥ 6) :
    7 * eulerNum n ≥ 19 * eulerDen n + 1 :=
  euler_lower_generic 19 7 6 (by decide) (by decide) n hn

/-! ### Upper bound meta-algorithm (symmetric) -/

/-- Inductive step for upper bound: `j · eulerDen k ≥ b · eulerNum k + 1`
    AND `k ≥ b` → `j · eulerDen (k+1) ≥ b · eulerNum (k+1) + 1`. -/
theorem euler_upper_step (j b k : Nat) (hk : k ≥ b)
    (h_inv : j * eulerDen k ≥ b * eulerNum k + 1) :
    j * eulerDen (k + 1) ≥ b * eulerNum (k + 1) + 1 := by
  show j * ((k + 1) * eulerDen k) ≥ b * ((k + 1) * eulerNum k + 1) + 1
  have h_lhs : j * ((k+1) * eulerDen k) = (k+1) * (j * eulerDen k) := by
    rw [← mul_assoc, Nat.mul_comm j (k+1), mul_assoc]
  have h_rhs : b * ((k+1) * eulerNum k + 1) + 1
             = (k+1) * (b * eulerNum k) + b + 1 := by
    rw [Nat.mul_add, Nat.mul_one, ← mul_assoc, Nat.mul_comm b (k+1), mul_assoc]
  rw [h_lhs, h_rhs]
  have h_mul : (k+1) * (j * eulerDen k) ≥ (k+1) * (b * eulerNum k + 1) :=
    Nat.mul_le_mul_left (k+1) h_inv
  have h_dist : (k+1) * (b * eulerNum k + 1)
              = (k+1) * (b * eulerNum k) + (k+1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [h_dist] at h_mul
  -- Need: (k+1) * (j · d_k) ≥ (k+1) * (b · a_k) + b + 1
  -- Have: (k+1) * (j · d_k) ≥ (k+1) * (b · a_k) + (k+1)
  -- So need (k+1) ≥ b + 1, i.e., k ≥ b.
  have h_kp1_ge : k + 1 ≥ b + 1 := Nat.succ_le_succ hk
  have h_target : (k+1) * (b * eulerNum k) + (k+1) ≥
                  (k+1) * (b * eulerNum k) + (b + 1) :=
    Nat.add_le_add_left h_kp1_ge _
  have h_unfold : (k+1) * (b * eulerNum k) + (b + 1)
                = (k+1) * (b * eulerNum k) + b + 1 := by
    rw [Nat.add_assoc]
  rw [h_unfold] at h_target
  exact Nat.le_trans h_target h_mul

/-- **Generic Euler upper bound (META-ALGORITHM)**: `S_n < j/b` strict
    for n ≥ max(N0, b). -/
theorem euler_upper_generic (j b N0 : Nat) (hb : b ≥ 1) (hN0 : N0 ≥ b)
    (h_base : j * eulerDen N0 ≥ b * eulerNum N0 + 1) :
    ∀ n, n ≥ N0 → j * eulerDen n ≥ b * eulerNum n + 1 := by
  intro n hn
  induction n with
  | zero =>
      have hN0_zero : N0 = 0 := Nat.le_zero.mp hn
      rw [hN0_zero] at h_base
      exact h_base
  | succ k ih =>
      rcases Nat.lt_or_ge k N0 with h_lt | h_ge
      · have h_kp1 : k + 1 = N0 := by
          have h2 : k + 1 ≤ N0 := h_lt
          exact Nat.le_antisymm h2 hn
        rw [h_kp1]; exact h_base
      · have h_inv := ih h_ge
        have h_k_ge_b : k ≥ b := Nat.le_trans hN0 h_ge
        exact euler_upper_step j b k h_k_ge_b h_inv

/-- Per-b upper: e < 9/3 = 3 (b=3, j=9, N0=3). -/
theorem e_lt_9_3 (n : Nat) (hn : n ≥ 3) :
    9 * eulerDen n ≥ 3 * eulerNum n + 1 :=
  euler_upper_generic 9 3 3 (by decide) (by decide) (by decide) n hn

/-- Per-b upper: e < 11/4 (b=4, j=11, N0=4). -/
theorem e_lt_11_4 (n : Nat) (hn : n ≥ 4) :
    11 * eulerDen n ≥ 4 * eulerNum n + 1 :=
  euler_upper_generic 11 4 4 (by decide) (by decide) (by decide) n hn

/-! ### Transcendental cut discriminator

`euler_lower_generic` + `euler_upper_generic` 결합 — 임의 (a, b) 의
e-discrimination 의 unified theorem. -/

/-- **Transcendental cut discriminator (lower side)**: 임의 (a, b) 에
    대해 j_low ≥ a 인 sharper lower 가 있 으 면, S_n > a/b strict
    for all n ≥ N0.

    e > a/b 의 partial-sum form. -/
theorem e_partial_gt_a_b (a b j_low N0 : Nat) (hb : b ≥ 1)
    (h_a_le_j : a ≤ j_low)
    (h_base : b * eulerNum N0 ≥ j_low * eulerDen N0 + 1) :
    ∀ n, n ≥ N0 → b * eulerNum n > a * eulerDen n := by
  intro n hn
  have h_lower := euler_lower_generic j_low b N0 hb h_base n hn
  -- h_lower : b · eulerNum n ≥ j_low · eulerDen n + 1
  -- a ≤ j_low → a · eulerDen n ≤ j_low · eulerDen n
  have h_amul : a * eulerDen n ≤ j_low * eulerDen n :=
    Nat.mul_le_mul_right (eulerDen n) h_a_le_j
  -- b · eulerNum n ≥ j_low · eulerDen n + 1 > j_low · eulerDen n ≥ a · eulerDen n
  have h_strict : j_low * eulerDen n + 1 > a * eulerDen n :=
    Nat.lt_succ_of_le h_amul
  exact Nat.lt_of_lt_of_le h_strict h_lower

/-- **Transcendental cut discriminator (upper side)**: a ≥ j_up 인
    sharper upper 가 있 으 면, S_n < a/b strict for all n ≥ N0.

    e < a/b 의 partial-sum form. -/
theorem e_partial_lt_a_b (a b j_up N0 : Nat) (hb : b ≥ 1) (hN0 : N0 ≥ b)
    (h_a_ge_j : a ≥ j_up)
    (h_base : j_up * eulerDen N0 ≥ b * eulerNum N0 + 1) :
    ∀ n, n ≥ N0 → a * eulerDen n > b * eulerNum n := by
  intro n hn
  have h_upper := euler_upper_generic j_up b N0 hb hN0 h_base n hn
  -- h_upper : j_up · eulerDen n ≥ b · eulerNum n + 1
  have h_amul : a * eulerDen n ≥ j_up * eulerDen n :=
    Nat.mul_le_mul_right (eulerDen n) h_a_ge_j
  have h_strict : a * eulerDen n + 1 > b * eulerNum n + 1 :=
    Nat.lt_succ_of_le (Nat.le_trans h_upper h_amul)
  exact Nat.lt_of_succ_lt_succ h_strict

/-- **e ≠ a/b** (partial-sum form): a/b 가 (j_low, j_up) interval 외 면
    e ≠ a/b in framework partial sum form. -/
theorem e_partial_neq_a_b (a b j_low j_up N0 : Nat) (hb : b ≥ 1) (hN0 : N0 ≥ b)
    (h_a_out : a ≤ j_low ∨ a ≥ j_up)
    (h_lower_base : b * eulerNum N0 ≥ j_low * eulerDen N0 + 1)
    (h_upper_base : j_up * eulerDen N0 ≥ b * eulerNum N0 + 1) :
    ∀ n, n ≥ N0 → b * eulerNum n ≠ a * eulerDen n := by
  intro n hn heq
  cases h_a_out with
  | inl h_le =>
      have h_gt := e_partial_gt_a_b a b j_low N0 hb h_le h_lower_base n hn
      rw [heq] at h_gt
      exact Nat.lt_irrefl _ h_gt
  | inr h_ge =>
      have h_lt := e_partial_lt_a_b a b j_up N0 hb hN0 h_ge h_upper_base n hn
      rw [heq] at h_lt
      exact Nat.lt_irrefl _ h_lt

/-! ### Demonstrations: e ≠ a/b for fixed b, all a -/

/-- **e ≠ a/3 for any a** via unified discriminator (j_low=8, j_up=9). -/
theorem e_neq_a_third (a : Nat) (n : Nat) (hn : n ≥ 4) :
    3 * eulerNum n ≠ a * eulerDen n := by
  apply e_partial_neq_a_b a 3 8 9 4 (by decide) (by decide) ?_
    (by decide) (by decide) n hn
  -- a ≤ 8 ∨ a ≥ 9
  rcases Nat.lt_or_ge a 9 with h | h
  · exact Or.inl (Nat.le_of_lt_succ h)
  · exact Or.inr h

/-- **e ≠ a/4 for any a** via unified discriminator (j_low=10, j_up=11). -/
theorem e_neq_a_quarter (a : Nat) (n : Nat) (hn : n ≥ 4) :
    4 * eulerNum n ≠ a * eulerDen n := by
  apply e_partial_neq_a_b a 4 10 11 4 (by decide) (by decide) ?_
    (by decide) (by decide) n hn
  rcases Nat.lt_or_ge a 11 with h | h
  · exact Or.inl (Nat.le_of_lt_succ h)
  · exact Or.inr h

end E213.Research.EulerGenericPure
