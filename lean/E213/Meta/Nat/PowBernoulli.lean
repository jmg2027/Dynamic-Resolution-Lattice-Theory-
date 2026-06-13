import E213.Meta.Nat.PowBasic
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Tactic.NatHelper

/-!
# PowBernoulli — additive Bernoulli bounds and the cross-degree power gap

Two ∅-axiom Bernoulli inequalities over `Nat`, stated additively (no truncated
subtraction):

    (N+1)^(s+1) ≤ N^(s+1) + (s+1)·(N+1)^s            (`bernoulli_upper`)
    N^(s+1) + (s+1)·N^s ≤ (N+1)^(s+1)                (`bernoulli_lower`)

and their consequence, the **cross-degree power gap** — the arithmetic crux of
the modulus-degree hierarchy: once the base outpaces the degree,

    K^e < (K-1)^(e+1)              whenever  e + 3 ≤ K    (`pow_pred_lt`)

i.e. a higher exponent on a base one smaller eventually dominates a lower
exponent on the larger base.  This is exactly the growth separation that lets a
degree-`(t+1)` probe schedule rescue a presentation the degree-`t` schedule
breaks (`Real213/RateHierarchy`).  `succ_pow_lt_succ_pow` is the calibration
fact `K^t + 1 < (K+1)^t` (`t ≥ 2`) used to read `rootFloor t (K^t + 1) = K`.

All zero-axiom.
-/

namespace E213.Meta.Nat.PowBernoulli

open E213.Meta.Nat.PowBasic (powBase_le one_le_pow)
open E213.Tactic.NatHelper (le_of_add_le_add_left add_mul)

/-- Cancel a common right summand in a `≤` (via commutation to the left). -/
private theorem le_of_add_le_add_right' {a b c : Nat} (h : a + c ≤ b + c) : a ≤ b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact le_of_add_le_add_left h

/-- The step of `bernoulli_upper`, as pure atom algebra: with `B = C·(N+1)`,
    `A ≤ B`, and the hypothesis `B ≤ A + (s+1)·C`, get `B·(N+1) ≤ A·N + (s+2)·B`. -/
private theorem bupper_core {A B C N s : Nat} (hBC : B = C * (N+1)) (hAB : A ≤ B)
    (hIH : B ≤ A + (s+1) * C) : B * (N+1) ≤ A * N + (s+1+1) * B := by
  calc B * (N+1)
      ≤ (A + (s+1) * C) * (N+1) := Nat.mul_le_mul_right _ hIH
    _ = A * N + A + (s+1) * B := by rw [hBC]; ring_nat
    _ ≤ A * N + B + (s+1) * B :=
        Nat.add_le_add_right (Nat.add_le_add_left hAB (A * N)) ((s+1) * B)
    _ = A * N + (s+1+1) * B := by ring_nat

/-- The step of `bernoulli_lower`, as pure atom algebra: with `A = c·N`, `A ≤ B`,
    and `A + (s+1)·c ≤ B`, get `A·N + (s+2)·A ≤ B·(N+1)`. -/
private theorem blower_core {A B c N s : Nat} (hAc : A = c * N) (hAB : A ≤ B)
    (hIH : A + (s+1) * c ≤ B) : A * N + (s+1+1) * A ≤ B * (N+1) := by
  have hi : A * N + (s+1) * A ≤ B * N := by
    calc A * N + (s+1) * A = (A + (s+1) * c) * N := by rw [hAc]; ring_nat
      _ ≤ B * N := Nat.mul_le_mul_right _ hIH
  calc A * N + (s+1+1) * A = (A * N + (s+1) * A) + A := by ring_nat
    _ ≤ B * N + B := Nat.add_le_add hi hAB
    _ = B * (N+1) := by rw [Nat.mul_succ]

/-- **Bernoulli, upper.**  `(N+1)^(s+1) ≤ N^(s+1) + (s+1)·(N+1)^s`. -/
theorem bernoulli_upper : ∀ (s N : Nat), (N+1)^(s+1) ≤ N^(s+1) + (s+1) * (N+1)^s
  | 0, N => by
      show (N+1)^1 ≤ N^1 + 1 * (N+1)^0
      rw [Nat.pow_one, Nat.pow_one, Nat.pow_zero, Nat.one_mul]
      exact Nat.le_refl _
  | s+1, N => by
      rw [Nat.pow_succ (N+1) (s+1), Nat.pow_succ N (s+1)]
      exact bupper_core (Nat.pow_succ (N+1) s) (powBase_le (Nat.le_succ N) (s+1))
        (bernoulli_upper s N)

/-- **Bernoulli, lower.**  `N^(s+1) + (s+1)·N^s ≤ (N+1)^(s+1)`. -/
theorem bernoulli_lower : ∀ (s N : Nat), N^(s+1) + (s+1) * N^s ≤ (N+1)^(s+1)
  | 0, N => by
      show N^1 + 1 * N^0 ≤ (N+1)^1
      rw [Nat.pow_one, Nat.pow_one, Nat.pow_zero, Nat.one_mul]
      exact Nat.le_refl _
  | s+1, N => by
      rw [Nat.pow_succ N (s+1), Nat.pow_succ (N+1) (s+1)]
      exact blower_core (Nat.pow_succ N s) (powBase_le (Nat.le_succ N) (s+1))
        (bernoulli_lower s N)

/-- **Cross-degree power gap.**  Once the (smaller) base `K` exceeds the
    exponent by at least `2`, raising the exponent by one on `K` strictly
    dominates the lower exponent on the larger base `K+1`:

        (K+1)^e < K^(e+1)              whenever  e + 2 ≤ K.

    Equivalently `(K+1)^e < ((K+1)-1)^(e+1)`: the discrete growth separation
    behind the strict modulus-degree ladder — the degree axis genuinely outruns
    the base axis. -/
theorem pow_pred_lt (e K : Nat) (hK : e + 2 ≤ K) : (K+1)^e < K^(e+1) := by
  have hb := bernoulli_upper e K       -- (K+1)^(e+1) ≤ K^(e+1) + (e+1)*(K+1)^e
  have hP1 : 1 ≤ (K+1)^e := one_le_pow (Nat.succ_le_succ (Nat.zero_le K)) e
  -- P*K ≤ Q + e*P, by cancelling one P off `hb`
  have hstep : (K+1)^e * K ≤ K^(e+1) + e * (K+1)^e := by
    have e1 : (K+1)^(e+1) = (K+1)^e * K + (K+1)^e := by
      rw [Nat.pow_succ, Nat.mul_succ]
    have e2 : K^(e+1) + (e+1) * (K+1)^e
        = (K^(e+1) + e * (K+1)^e) + (K+1)^e := by
      rw [Nat.succ_mul, Nat.add_assoc]
    rw [e1, e2] at hb
    exact le_of_add_le_add_right' hb
  -- e*P + 2*P ≤ P*K (from e+2 ≤ K)
  have hlow : e * (K+1)^e + 2 * (K+1)^e ≤ (K+1)^e * K := by
    have h : (e + 2) * (K+1)^e ≤ K * (K+1)^e := Nat.mul_le_mul_right _ hK
    rwa [add_mul, Nat.mul_comm K ((K+1)^e)] at h
  -- chain and cancel e*P, then P < 2*P ≤ Q
  have h2P : 2 * (K+1)^e ≤ K^(e+1) := by
    have hchain : e * (K+1)^e + 2 * (K+1)^e ≤ K^(e+1) + e * (K+1)^e :=
      Nat.le_trans hlow hstep
    rw [Nat.add_comm (e * (K+1)^e) (2 * (K+1)^e)] at hchain
    exact le_of_add_le_add_right' hchain
  have hlt : (K+1)^e < 2 * (K+1)^e := by
    rw [Nat.two_mul]; exact Nat.lt_add_of_pos_right hP1
  exact Nat.lt_of_lt_of_le hlt h2P

/-- Calibration for the schedule read-back: for `t ≥ 2`, `K^t + 1` is strictly
    below `(K+1)^t`, so `rootFloor t (K^t + 1) = K`.  Uses the lower-Bernoulli
    surplus `t·K^(t-1) ≥ 2`. -/
theorem succ_pow_lt_succ_pow (t K : Nat) (ht : 2 ≤ t) (hK : 1 ≤ K) :
    K^t + 1 < (K+1)^t := by
  match t, ht with
  | e+2, _ =>
    have hbl := bernoulli_lower (e+1) K   -- K^(e+2) + (e+2)*K^(e+1) ≤ (K+1)^(e+2)
    have hsurplus : 2 ≤ (e+2) * K^(e+1) := by
      have h : 2 * 1 ≤ (e+2) * K^(e+1) :=
        Nat.mul_le_mul (Nat.le_add_left 2 e) (one_le_pow hK (e+1))
      rwa [Nat.mul_one] at h
    calc K^(e+2) + 1
        < K^(e+2) + (e+2) * K^(e+1) := Nat.add_lt_add_left hsurplus _
      _ ≤ (K+1)^(e+2) := hbl

end E213.Meta.Nat.PowBernoulli
