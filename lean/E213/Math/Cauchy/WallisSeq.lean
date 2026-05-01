import E213.Math.Cauchy.PellSeq
import E213.Math.Cauchy.Archimedean
import E213.Math.Cauchy.MonotonicBounded

/-!
# Research.WallisSeq: π/2 Dedekind cut via Wallis product

Wallis product partial form for π/2:

  π/2 = ∏_{k=1}^∞ (2k)² / ((2k-1)(2k+1))

Partial products:
- W_n = ∏_{k=1..n} (2k)² / ((2k-1)(2k+1))
- W_0 = 1, W_1 = 4/3, W_2 = 64/45, ... → π/2 ≈ 1.5708.

`wallisNum`, `wallisDen` integer recursion.

## Invariants (all closed)

- **Monotonic**: `wallisNum n * wallisDen (n+1) < wallisNum (n+1) * wallisDen n`.
  W_n strictly increasing.
- **Lower** (n ≥ 1): `3 * wallisNum n ≥ 4 * wallisDen n`.
  (W_n ≥ 4/3 > 1 from n=1.)
- **Upper**: `wallisNum n * (2n+1) ≤ (4n+1) * wallisDen n`
  (W_n ≤ 2 - 1/(2n+1) < 2).  Polynomial identity
  `(4k+1)*4(k+1)² + 1 = (4k+5)*(2k+1)²` (degree-3 in k) closed
  via **Flat-Monomial Strategy**: `K := k*k`, `M := k*(k*k)`
  two-generalize + `Nat.mul_mul_mul_comm` + omega (proposed by Mingu,
  note 72).  Lean 4 core only — no `ring`.

Therefore, both sides of the W_n ∈ (1, 2) Dedekind cut are fully
demonstrated:
- m/k ≤ 1 → orderProj false (n ≥ 1).  [closed]
- m/k ≥ 2 → orderProj true (∀ n).  [closed]

## Significance

Together with EulerSeq (Σ 1/k!), a 213 Cauchy demonstration in the
transcendental domain.  e: factorial denominator.  π: even²/odd² product.

`#print axioms`: [propext] only.

## Changelog

- 2026-04-25: WallisSeq.lean written.  π/2 ∈ (1, 2) cuts.
-/

namespace E213.Math.Cauchy.WallisSeq

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

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

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

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-! ### Monotonicity (partial Cauchy demonstration) -/

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

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

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

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

open E213.Firmware E213.Hypervisor

/-! ### Upper invariant via Flat-Monomial Strategy -/

/-- **Polynomial identity**: `(4k+1) · 4(k+1)² + 1 = (4k+5) · (2k+1)²`.

    Closed without ring in Lean 4 core — flat-monomial normalization
    + two-generalize (`K := k*k`, `M := k*(k*k)`) + omega.
    Minimal instance of the strategy from note 72. -/
theorem wallis_poly_identity (k : Nat) :
    (4 * k + 1) * (4 * (k + 1) * (k + 1)) + 1
      = (4 * k + 5) * ((2 * k + 1) * (2 * k + 1)) := by
  have h_kp1_sq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
    rw [Nat.mul_add (k+1) k 1, Nat.mul_one, Nat.add_mul k 1 k, Nat.one_mul]
    omega
  have h_2kp1_sq : (2 * k + 1) * (2 * k + 1) = 4 * (k * k) + 4 * k + 1 := by
    rw [Nat.mul_add (2*k+1) (2*k) 1, Nat.mul_one,
        Nat.add_mul (2*k) 1 (2*k), Nat.one_mul]
    rw [show 2 * k * (2 * k) = 4 * (k * k) from Nat.mul_mul_mul_comm 2 k 2 k]
    omega
  rw [show 4 * (k+1) * (k+1) = 4 * ((k+1) * (k+1)) from Nat.mul_assoc _ _ _]
  rw [h_kp1_sq, h_2kp1_sq]
  rw [show 4 * (k*k + 2*k + 1) = 4*(k*k) + 8*k + 4 by
        rw [Nat.mul_add, Nat.mul_add]; omega]
  have hLHS : (4*k + 1) * (4*(k*k) + 8*k + 4)
            = 16*(k*(k*k)) + 32*(k*k) + 16*k + 4*(k*k) + 8*k + 4 := by
    rw [Nat.add_mul (4*k) 1, Nat.one_mul]
    rw [Nat.mul_add (4*k) (4*(k*k) + 8*k) 4]
    rw [Nat.mul_add (4*k) (4*(k*k)) (8*k)]
    rw [show 4*k*(4*(k*k)) = 16*(k*(k*k)) from Nat.mul_mul_mul_comm 4 k 4 (k*k)]
    rw [show 4*k*(8*k) = 32*(k*k) from Nat.mul_mul_mul_comm 4 k 8 k]
    rw [show 4*k*4 = 16*k from by rw [Nat.mul_comm (4*k) 4, ← Nat.mul_assoc]]
    omega
  have hRHS : (4*k + 5) * (4*(k*k) + 4*k + 1)
            = 16*(k*(k*k)) + 16*(k*k) + 4*k + 20*(k*k) + 20*k + 5 := by
    rw [Nat.add_mul (4*k) 5]
    rw [Nat.mul_add (4*k) (4*(k*k) + 4*k) 1, Nat.mul_add (4*k) (4*(k*k)) (4*k)]
    rw [Nat.mul_add 5 (4*(k*k) + 4*k) 1, Nat.mul_add 5 (4*(k*k)) (4*k)]
    rw [Nat.mul_one (4*k), Nat.mul_one 5]
    rw [show 4*k*(4*(k*k)) = 16*(k*(k*k)) from Nat.mul_mul_mul_comm 4 k 4 (k*k)]
    rw [show 4*k*(4*k) = 16*(k*k) from Nat.mul_mul_mul_comm 4 k 4 k]
    rw [show 5*(4*(k*k)) = 20*(k*k) by rw [← Nat.mul_assoc]]
    rw [show (5:Nat)*(4*k) = 20*k by rw [← Nat.mul_assoc]]
    omega
  rw [hLHS, hRHS]
  generalize k * (k * k) = M
  generalize k * k = K
  omega

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-- **Upper invariant**: `wallisNum n * (2n+1) ≤ (4n+1) * wallisDen n`.
    (W_n ≤ 2 - 1/(2n+1) < 2.)

    Strategy: IH multiplied by 4(k+1)², chain via `wallis_poly_identity`,
    then cancel (2k+1) at the end via `Nat.le_of_mul_le_mul_left`. -/
theorem wallis_upper_inv (n : Nat) :
    wallisNum n * (2 * n + 1) ≤ (4 * n + 1) * wallisDen n := by
  induction n with
  | zero => decide
  | succ k ih =>
      show (wallisNum k * (4 * (k+1) * (k+1))) * (2*k + 3)
            ≤ (4*k + 5) * (wallisDen k * ((2*k+1) * (2*k+3)))
      -- Abstract via generalize.  Naming: N=W_k, D=D_k, P=4(k+1)², Q=2k+1,
      -- R=2k+3, S=4k+5, T=4k+1.
      have h_poly : (4*k + 1) * (4 * (k+1) * (k+1)) + 1
                  = (4*k + 5) * ((2*k+1) * (2*k+1)) := wallis_poly_identity k
      have hQ_pos : 0 < 2*k + 1 := by omega
      generalize hP : 4 * (k+1) * (k+1) = P at *
      generalize hQ : 2*k + 1 = Q at *
      generalize hR : 2*k + 3 = R at *
      generalize hS : 4*k + 5 = S at *
      generalize hT : 4*k + 1 = T at *
      generalize hN : wallisNum k = N at *
      generalize hD : wallisDen k = D at *
      -- Now: ih : N * Q ≤ T * D.  h_poly : T * P + 1 = S * (Q * Q).
      -- Goal: N * P * R ≤ S * (D * (Q * R)).  hQ_pos : 0 < Q.
      have h_poly_le : T * P ≤ S * Q * Q := by
        have hsq : S * (Q * Q) = S * Q * Q := (Nat.mul_assoc _ _ _).symm
        omega
      have h1 : N * Q * P ≤ T * D * P := Nat.mul_le_mul_right P ih
      have h2 : T * D * P = D * (T * P) := by
        rw [Nat.mul_comm T D, Nat.mul_assoc]
      have h3 : D * (T * P) ≤ D * (S * Q * Q) := Nat.mul_le_mul_left D h_poly_le
      have h4 : N * Q * P ≤ D * (S * Q * Q) := by
        rw [h2] at h1; exact Nat.le_trans h1 h3
      have h5 : N * Q * P * R ≤ D * (S * Q * Q) * R :=
        Nat.mul_le_mul_right R h4
      have hLHS_assoc : N * Q * P * R = N * P * R * Q := by
        have e1 : N * Q * P = N * P * Q := by
          rw [Nat.mul_assoc N Q P, Nat.mul_comm Q P, ← Nat.mul_assoc]
        rw [e1]
        rw [Nat.mul_assoc (N*P) Q R, Nat.mul_comm Q R, ← Nat.mul_assoc]
      have hRHS_assoc : D * (S * Q * Q) * R = S * D * Q * R * Q := by
        have e2 : D * (S * Q * Q) = S * D * Q * Q := by
          rw [← Nat.mul_assoc D (S*Q) Q, ← Nat.mul_assoc D S Q, Nat.mul_comm D S]
        rw [e2]
        rw [Nat.mul_assoc (S*D*Q) Q R, Nat.mul_comm Q R, ← Nat.mul_assoc]
      rw [hLHS_assoc, hRHS_assoc] at h5
      have h6 : Q * (N * P * R) ≤ Q * (S * D * Q * R) := by
        rw [Nat.mul_comm Q (N * P * R), Nat.mul_comm Q (S * D * Q * R)]
        exact h5
      have h7 : N * P * R ≤ S * D * Q * R :=
        Nat.le_of_mul_le_mul_left h6 hQ_pos
      have hRHS_goal : S * (D * (Q * R)) = S * D * Q * R := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc]
      rw [hRHS_goal]
      exact h7

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-- **Cut above 2**: m/k ≥ 2 (2k ≤ m) → orderProj true (∀ n).
    Upper inv: a_n * (2n+1) ≤ (4n+1) * d_n.  (4n+1) ≤ 2(2n+1) so
    a_n * (2n+1) ≤ 2 * (2n+1) * d_n, cancel (2n+1): a_n ≤ 2 d_n.
    Then a_n * k ≤ 2 d_n * k = d_n * (2k) ≤ d_n * m. -/
theorem wallis_orderProj_above_2 (m k : Nat) (h2km : 2 * k ≤ m) (n : Nat) :
    orderProj m k (abLens.view (wallisRaw n).val) = true := by
  rw [wallisRaw_view]
  unfold orderProj
  show decide (wallisNum n * k ≤ wallisDen n * m) = true
  rw [decide_eq_true_iff]
  -- From upper inv: W_n * (2n+1) ≤ (4n+1) * D_n.
  -- (4n+1) ≤ 2*(2n+1) - 1, so W_n * (2n+1) ≤ (2*(2n+1) - 1) * D_n < 2*(2n+1)*D_n.
  -- Hence W_n * (2n+1) ≤ 2 * D_n * (2n+1) - D_n.
  -- Cancel (2n+1): W_n ≤ 2 * D_n (with strict, or ≤ - 1, but use ≤ form).
  -- Cleaner: from W_n * (2n+1) ≤ (4n+1)*D_n ≤ 2(2n+1)*D_n - D_n, so
  -- W_n * (2n+1) < 2*(2n+1)*D_n, which cancels (2n+1) > 0: W_n < 2*D_n.
  -- For Nat: W_n + 1 ≤ 2 * D_n, hence W_n ≤ 2 * D_n.
  have hu := wallis_upper_inv n
  have h_2n1_pos : 0 < 2*n + 1 := by omega
  -- (4n+1) = 2*(2n+1) - 1, so (4n+1) * D_n + D_n = 2 * (2n+1) * D_n.
  have h_eq : (4*n + 1) * wallisDen n + wallisDen n
              = 2 * (2*n + 1) * wallisDen n := by
    have h_e : 2 * (2*n + 1) = (4*n + 1) + 1 := by omega
    rw [h_e, Nat.add_mul (4*n + 1) 1 (wallisDen n), Nat.one_mul]
  -- So W_n * (2n+1) + D_n ≤ 2 * (2n+1) * D_n.
  have h1 : wallisNum n * (2*n + 1) + wallisDen n ≤ 2 * (2*n + 1) * wallisDen n := by
    rw [← h_eq]
    exact Nat.add_le_add_right hu (wallisDen n)
  -- Hence W_n * (2n+1) ≤ 2 * D_n * (2n+1).
  have h2 : wallisNum n * (2*n+1) ≤ 2 * wallisDen n * (2*n+1) := by
    have hdpos : 1 ≤ wallisDen n := wallisDen_pos n
    have h_RHS : 2 * (2*n+1) * wallisDen n = 2 * wallisDen n * (2*n+1) := by
      rw [Nat.mul_assoc, Nat.mul_comm (2*n+1) (wallisDen n), ← Nat.mul_assoc]
    rw [h_RHS] at h1
    omega
  -- Cancel (2n+1): W_n ≤ 2 * D_n.
  have h3 : (2*n+1) * wallisNum n ≤ (2*n+1) * (2 * wallisDen n) := by
    rw [Nat.mul_comm (2*n+1) (wallisNum n), Nat.mul_comm (2*n+1) (2 * wallisDen n)]
    exact h2
  have h4 : wallisNum n ≤ 2 * wallisDen n :=
    Nat.le_of_mul_le_mul_left h3 h_2n1_pos
  -- Now goal: W_n * k ≤ D_n * m.  W_n * k ≤ 2 * D_n * k = D_n * (2*k) ≤ D_n * m.
  have h5 : wallisNum n * k ≤ 2 * wallisDen n * k := Nat.mul_le_mul_right k h4
  have h6 : 2 * wallisDen n * k = wallisDen n * (2 * k) := by
    rw [Nat.mul_comm 2 (wallisDen n), Nat.mul_assoc]
  rw [h6] at h5
  have h7 : wallisDen n * (2 * k) ≤ wallisDen n * m :=
    Nat.mul_le_mul_left (wallisDen n) h2km
  exact Nat.le_trans h5 h7

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-- **Order Cauchy** at thresholds m/k ≥ 2 ∨ m/k ≤ 1.
    Other thresholds in (1, 2) — fine-grained analysis would need
    convergence rate to π/2 ≈ 1.5708. -/
theorem wallis_orderCauchy_at_concrete (m k : Nat) (hk : k ≥ 1)
    (hcase : 2 * k ≤ m ∨ m ≤ k) :
    ∃ N, ∀ p q, p ≥ N → q ≥ N →
      orderProj m k (abLens.view (wallisRaw p).val)
        = orderProj m k (abLens.view (wallisRaw q).val) := by
  refine ⟨1, ?_⟩
  intro p q hp hq
  rcases hcase with h2km | hmk
  · rw [wallis_orderProj_above_2 m k h2km p,
        wallis_orderProj_above_2 m k h2km q]
  · rw [wallis_orderProj_below_1 m k hk hmk p hp,
        wallis_orderProj_below_1 m k hk hmk q hq]

end E213.Math.Cauchy.WallisSeq

namespace E213.Math.Cauchy.WallisSeq

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy
open E213.Research.MonotonicBoundedCauchy

/-! ### Monotonicity instance (for MonotonicBoundedCauchy) -/

/-- Wallis Raw sequence as `Nat → Raw`. -/
def wallisRawSeq : Nat → Raw := fun n => (wallisRaw n).val

/-- Wallis seq is ab-monotonic (W_n ≤ W_{n+1}).  Same key inequality
    `(2k+1)(2k+3) ≤ 4(k+1)²` as in `wallis_lower_inv`. -/
theorem wallis_isAbMonotonic : IsAbMonotonic wallisRawSeq := by
  intro n
  show (abLens.view (wallisRaw n).val).1 * (abLens.view (wallisRaw (n+1)).val).2
       ≤ (abLens.view (wallisRaw (n+1)).val).1 * (abLens.view (wallisRaw n).val).2
  rw [wallisRaw_view, wallisRaw_view]
  show wallisNum n * wallisDen (n+1) ≤ wallisNum (n+1) * wallisDen n
  show wallisNum n * (wallisDen n * ((2 * n + 1) * (2 * n + 3)))
       ≤ wallisNum n * (4 * (n + 1) * (n + 1)) * wallisDen n
  -- Goal: N * (D * P) ≤ (N * Q) * D where P = (2n+1)(2n+3), Q = 4(n+1)².
  -- Since P ≤ Q (poly identity), N * D * P ≤ N * D * Q = (N * Q) * D.
  have hkk : (2 * n + 1) * (2 * n + 3) ≤ 4 * (n + 1) * (n + 1) := by
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
  -- N * (D * P) = N * D * P ≤ N * D * Q = (N * Q) * D  (= goal RHS reassoc).
  have hLHS : wallisNum n * (wallisDen n * ((2 * n + 1) * (2 * n + 3)))
              = wallisNum n * wallisDen n * ((2 * n + 1) * (2 * n + 3)) :=
    (Nat.mul_assoc _ _ _).symm
  have hRHS : wallisNum n * (4 * (n + 1) * (n + 1)) * wallisDen n
              = wallisNum n * wallisDen n * (4 * (n + 1) * (n + 1)) := by
    rw [Nat.mul_assoc, Nat.mul_comm (4 * (n + 1) * (n + 1)) (wallisDen n),
        ← Nat.mul_assoc]
  rw [hLHS, hRHS]
  exact Nat.mul_le_mul_left (wallisNum n * wallisDen n) hkk

/-- Wallis seq has positive denominators. -/
theorem wallis_isAbPositiveB : IsAbPositiveB wallisRawSeq := by
  intro n
  show 1 ≤ (abLens.view (wallisRaw n).val).2
  rw [wallisRaw_view]
  exact wallisDen_pos n

end E213.Math.Cauchy.WallisSeq
