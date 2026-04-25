import E213.Research.PellSeq
import E213.Research.ArchimedeanCauchy

/-!
# Research.WallisSeq: π/2 Dedekind cut via Wallis product

Wallis product partial form for π/2:

  π/2 = ∏_{k=1}^∞ (2k)² / ((2k-1)(2k+1))

Partial products:
- W_n = ∏_{k=1..n} (2k)² / ((2k-1)(2k+1))
- W_0 = 1, W_1 = 4/3, W_2 = 64/45, ... → π/2 ≈ 1.5708.

`wallisNum`, `wallisDen` 정수 recursion.

## 불변량

- **Monotonic**: `wallisNum n * wallisDen (n+1) < wallisNum (n+1) * wallisDen n`.
  W_n strictly increasing.
- **Lower** (n ≥ 1): `3 * wallisNum n ≥ 4 * wallisDen n`.
  (W_n ≥ 4/3 > 1 from n=1.)
- **Upper** (deferred): `wallisNum n * (2n+1) ≤ (4n+1) * wallisDen n`.
  (W_n ≤ 2 - 1/(2n+1) < 2.)  Polynomial identity
  `(4k+1)*4(k+1)² + 1 = (4k+5)*(2k+1)²` (degree-3 in k) needs
  flat-monomial normalization layer in Lean 4 core (no `ring`).
  See note 72 for strategy.

따라서 현재 단계 demonstration:
- m/k ≤ 1 → orderProj false (n ≥ 1).  [closed]
- m/k ≥ 2 → orderProj true.  [pending upper invariant]

## 의의

EulerSeq (Σ 1/k!) 와 함께 transcendental 영역 의 213 Cauchy
demonstration.  e: factorial 분모.  π: even²/odd² product.

`#print axioms`: [propext] only.

## 변경 이력

- 2026-04-25: WallisSeq.lean 작성.  π/2 ∈ (1, 2) cuts.
-/

namespace E213.Research.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy
open E213.Research.PellSeq

/-! ### Wallis product recursion -/

/-- Numerator: wallisNum (n+1) = wallisNum n * 4 * (n+1)².  W_0 = 1. -/
def wallisNum : Nat → Nat
  | 0 => 1
  | n + 1 => wallisNum n * (4 * (n + 1) * (n + 1))

/-- Denominator: wallisDen (n+1) = wallisDen n * (2n+1) * (2n+3).  W_0 = 1. -/
def wallisDen : Nat → Nat
  | 0 => 1
  | n + 1 => wallisDen n * ((2 * n + 1) * (2 * n + 3))

theorem wallisNum_pos (n : Nat) : 1 ≤ wallisNum n := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 1 ≤ wallisNum k * (4 * (k + 1) * (k + 1))
      calc 1 = 1 * 1 := rfl
        _ ≤ wallisNum k * (4 * (k + 1) * (k + 1)) :=
            Nat.mul_le_mul ih (by
              have h1 : 1 ≤ 4 * (k + 1) := by
                calc 1 ≤ 4 := by decide
                  _ = 4 * 1 := by rw [Nat.mul_one]
                  _ ≤ 4 * (k + 1) := Nat.mul_le_mul_left 4 (by omega)
              calc 1 = 1 * 1 := rfl
                _ ≤ 4 * (k + 1) * (k + 1) := Nat.mul_le_mul h1 (by omega))

theorem wallisDen_pos (n : Nat) : 1 ≤ wallisDen n := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 1 ≤ wallisDen k * ((2 * k + 1) * (2 * k + 3))
      have h1 : 1 ≤ (2 * k + 1) * (2 * k + 3) := by
        calc 1 = 1 * 1 := rfl
          _ ≤ (2 * k + 1) * (2 * k + 3) := Nat.mul_le_mul (by omega) (by omega)
      calc 1 = 1 * 1 := rfl
        _ ≤ wallisDen k * ((2 * k + 1) * (2 * k + 3)) := Nat.mul_le_mul ih h1

end E213.Research.WallisSeq

namespace E213.Research.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-! ### Algebraic invariants -/

/-- **Lower invariant** (n ≥ 1): 3 * wallisNum n ≥ 4 * wallisDen n.
    (W_n ≥ 4/3 from n=1; monotonic increasing.)
    Base n=1: 3*4 = 12 ≥ 4*3 = 12 ✓.
    Step: W_{n+1}/W_n = 4(n+1)²/((2n+1)(2n+3)) ≥ 1 (i.e.,
          4(n+1)² ≥ (2n+1)(2n+3) iff 4n² + 8n + 4 ≥ 4n² + 8n + 3 ✓). -/
theorem wallis_lower_inv (n : Nat) (hn : n ≥ 1) :
    3 * wallisNum n ≥ 4 * wallisDen n := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst hk
        show 3 * wallisNum 1 ≥ 4 * wallisDen 1
        decide
      · have hk1 : k ≥ 1 := by omega
        have h_inv : 4 * wallisDen k ≤ 3 * wallisNum k := ih hk1
        show 4 * wallisDen (k + 1) ≤ 3 * wallisNum (k + 1)
        show 4 * (wallisDen k * ((2 * k + 1) * (2 * k + 3)))
              ≤ 3 * (wallisNum k * (4 * (k + 1) * (k + 1)))
        have hkk : (2 * k + 1) * (2 * k + 3) ≤ 4 * (k + 1) * (k + 1) := by
          have eL_h1 : 4 * (k + 1) * (k + 1)
                     = 4 * k * k + 4 * k * 1 + (4 * 1 * k + 4 * 1 * 1) := by
            rw [Nat.mul_add 4 k 1, Nat.add_mul, Nat.mul_add, Nat.mul_add]
          have eR_h1 : (2 * k + 1) * (2 * k + 3)
                     = 2 * k * (2 * k) + 2 * k * 3 + (1 * (2 * k) + 1 * 3) := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
          have e_kk_4 : 4 * k * k = 4 * (k * k) := by rw [Nat.mul_assoc]
          have e_kk_2 : 2 * k * (2 * k) = 4 * (k * k) := by
            rw [Nat.mul_mul_mul_comm]
          rw [eL_h1, eR_h1, e_kk_4, e_kk_2]
          omega
        -- Reassociate: 4 * (D * Q) = (4 * D) * Q,  3 * (N * P) = (3 * N) * P.
        have hLB : 4 * (wallisDen k * ((2 * k + 1) * (2 * k + 3)))
                   = (4 * wallisDen k) * ((2 * k + 1) * (2 * k + 3)) :=
          (Nat.mul_assoc _ _ _).symm
        have hLA : 3 * (wallisNum k * (4 * (k + 1) * (k + 1)))
                   = (3 * wallisNum k) * (4 * (k + 1) * (k + 1)) :=
          (Nat.mul_assoc _ _ _).symm
        rw [hLA, hLB]
        -- (4 D) * (2k+1)(2k+3) ≤ (3 N) * (2k+1)(2k+3) ≤ (3 N) * 4(k+1)².
        have step1 : (4 * wallisDen k) * ((2 * k + 1) * (2 * k + 3))
                     ≤ (3 * wallisNum k) * ((2 * k + 1) * (2 * k + 3)) :=
          Nat.mul_le_mul_right _ h_inv
        have step2 : (3 * wallisNum k) * ((2 * k + 1) * (2 * k + 3))
                     ≤ (3 * wallisNum k) * (4 * (k + 1) * (k + 1)) :=
          Nat.mul_le_mul_left (3 * wallisNum k) hkk
        exact Nat.le_trans step1 step2

end E213.Research.WallisSeq

namespace E213.Research.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-! ### Monotonicity (Cauchy 의 부분 demonstration) -/

/-- **Monotonicity**: W_n < W_{n+1}.
    wallisNum n * wallisDen (n+1) < wallisNum (n+1) * wallisDen n.
    Diff = wallisNum n * wallisDen n * 1 (since 4(k+1)² - (2k+1)(2k+3) = 1). -/
theorem wallis_monotonic (n : Nat) :
    wallisNum n * wallisDen (n + 1) < wallisNum (n + 1) * wallisDen n := by
  show wallisNum n * (wallisDen n * ((2 * n + 1) * (2 * n + 3)))
       < wallisNum n * (4 * (n + 1) * (n + 1)) * wallisDen n
  have hkk_strict : (2 * n + 1) * (2 * n + 3) < 4 * (n + 1) * (n + 1) := by
    have eL_h1 : 4 * (n + 1) * (n + 1)
               = 4 * n * n + 4 * n * 1 + (4 * 1 * n + 4 * 1 * 1) := by
      rw [Nat.mul_add 4 n 1, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have eR_h1 : (2 * n + 1) * (2 * n + 3)
               = 2 * n * (2 * n) + 2 * n * 3 + (1 * (2 * n) + 1 * 3) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have e_kk_4 : 4 * n * n = 4 * (n * n) := by rw [Nat.mul_assoc]
    have e_kk_2 : 2 * n * (2 * n) = 4 * (n * n) := by
      rw [Nat.mul_mul_mul_comm]
    rw [eL_h1, eR_h1, e_kk_4, e_kk_2]
    omega
  -- Reassociate and chain.
  have hL : wallisNum n * (wallisDen n * ((2 * n + 1) * (2 * n + 3)))
            = wallisNum n * wallisDen n * ((2 * n + 1) * (2 * n + 3)) := by
    rw [← Nat.mul_assoc]
  have hR : wallisNum n * (4 * (n + 1) * (n + 1)) * wallisDen n
            = wallisNum n * wallisDen n * (4 * (n + 1) * (n + 1)) := by
    rw [Nat.mul_assoc, Nat.mul_comm (4 * (n+1) * (n+1)) (wallisDen n),
        ← Nat.mul_assoc]
  rw [hL, hR]
  have h_pos : 1 ≤ wallisNum n * wallisDen n := by
    calc 1 = 1 * 1 := rfl
      _ ≤ wallisNum n * wallisDen n :=
          Nat.mul_le_mul (wallisNum_pos n) (wallisDen_pos n)
  exact Nat.mul_lt_mul_of_pos_left hkk_strict h_pos

end E213.Research.WallisSeq

namespace E213.Research.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy
open E213.Research.PellSeq

/-! ### Raw sequence + orderProj (below 1) cut -/

/-- **Wallis Raw sequence**: abLens.view (wallisRaw n) = (wallisNum n, wallisDen n). -/
def wallisRaw (n : Nat) :
    {r : Raw // abLens.view r = (wallisNum n, wallisDen n)} :=
  abLens_witness (wallisNum n + wallisDen n) (wallisNum n) (wallisDen n) rfl
    (wallisNum_pos n) (wallisDen_pos n)

theorem wallisRaw_view (n : Nat) :
    abLens.view (wallisRaw n).val = (wallisNum n, wallisDen n) :=
  (wallisRaw n).property

/-- **Cut below 1**: m/k ≤ 1 (m ≤ k) → orderProj false (n ≥ 1).
    From lower invariant: 3 * W_n ≥ 4 * D_n, so W_n > D_n ≥ D_n * (m/k).
    Concretely: a_n * k ≥ (4 * D_n / 3) * k > D_n * m. -/
theorem wallis_orderProj_below_1 (m k : Nat) (hk : k ≥ 1) (hmk : m ≤ k)
    (n : Nat) (hn : n ≥ 1) :
    orderProj m k (abLens.view (wallisRaw n).val) = false := by
  rw [wallisRaw_view]
  unfold orderProj
  show decide (wallisNum n * k ≤ wallisDen n * m) = false
  rw [decide_eq_false_iff_not]
  intro hle
  -- hle: a_n * k ≤ d_n * m.
  -- Lower inv: 3 * a_n ≥ 4 * d_n, i.e., a_n ≥ (4/3) d_n.
  -- a_n * k ≥ (in some sense) (4/3) d_n * k > d_n * k ≥ d_n * m.  Contradiction.
  have hl := wallis_lower_inv n hn
  -- 3 * a_n ≥ 4 * d_n.  Multiply hle by 3: 3 * (a_n * k) ≤ 3 * (d_n * m).
  -- 3 * a_n * k ≤ 3 * d_n * m.  And 4 * d_n * k ≤ 3 * a_n * k (from lower inv * k).
  -- So 4 * d_n * k ≤ 3 * d_n * m.
  -- m ≤ k implies 3 * d_n * m ≤ 3 * d_n * k.  So 4 * d_n * k ≤ 3 * d_n * k.
  -- Cancel d_n * k > 0: 4 ≤ 3.  Contra.
  have h1 : 4 * wallisDen n * k ≤ 3 * wallisNum n * k :=
    Nat.mul_le_mul_right k hl
  have h2 : 3 * (wallisNum n * k) ≤ 3 * (wallisDen n * m) :=
    Nat.mul_le_mul_left 3 hle
  have h2' : 3 * wallisNum n * k = 3 * (wallisNum n * k) := Nat.mul_assoc _ _ _
  have h3 : 4 * wallisDen n * k ≤ 3 * (wallisDen n * m) := by
    rw [h2'] at h1; exact Nat.le_trans h1 h2
  have h4 : 3 * (wallisDen n * m) ≤ 3 * (wallisDen n * k) :=
    Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (wallisDen n) hmk)
  have h5 : 4 * wallisDen n * k ≤ 3 * (wallisDen n * k) := Nat.le_trans h3 h4
  -- 4 * d * k ≤ 3 * (d * k), with d ≥ 1, k ≥ 1.  Contra.
  have hdpos : 1 ≤ wallisDen n := wallisDen_pos n
  have hdk : 1 ≤ wallisDen n * k := by
    calc 1 = 1 * 1 := rfl
      _ ≤ wallisDen n * k := Nat.mul_le_mul hdpos hk
  have h5' : 4 * (wallisDen n * k) ≤ 3 * (wallisDen n * k) := by
    rw [show 4 * wallisDen n * k = 4 * (wallisDen n * k) from Nat.mul_assoc _ _ _] at h5
    exact h5
  -- 4*X ≤ 3*X with X ≥ 1: contra.
  have h_swap : (wallisDen n * k) * 4 ≤ (wallisDen n * k) * 3 := by
    rw [Nat.mul_comm (wallisDen n * k) 4, Nat.mul_comm (wallisDen n * k) 3]
    exact h5'
  have h43 : 4 ≤ 3 :=
    Nat.le_of_mul_le_mul_left h_swap (by omega : 0 < wallisDen n * k)
  omega

end E213.Research.WallisSeq
