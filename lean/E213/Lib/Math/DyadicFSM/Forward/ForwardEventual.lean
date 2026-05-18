import E213.Lib.Math.DyadicFSM.Forward.ForwardClosure
import E213.Meta.Nat.EncodePair213
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
import E213.Lib.Math.DyadicFSM.Signature.Signature
/-!
# Forward direction (eventual): eventually periodic bits ⇒
  eventually periodic signature

Strict generalisation of `signature_eventually_periodic_of_periodic_bits`:
the bit stream may have a *pre-period* `N₀` before becoming periodic.

Proof structure mirrors the purely-periodic case but with offset:
joint state (sig (N₀ + k), k mod p) over k ∈ Fin (5p+1) collides
by pigeonhole; periodicity follows from N₀ + i onwards.

All theorems at PURE (∅-axiom; verified 2026-05-18).
-/

namespace E213.Lib.Math.DyadicFSM.Forward.ForwardEventual

open E213.Lib.Math.DyadicFSM.Signature.Signature (signature nextVertex)
open E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
  (pigeonhole_collision collisionTest collTest_imp_val_eq encode_inj)
open E213.Lib.Math.DyadicFSM.Forward.ForwardClosure (sub_is_multiple_of_p)

/-- bs eventually periodic at multiple of p, from N₀ onwards.
    STRICT ∅-AXIOM. -/
theorem bs_periodic_multiple_from (bs : Nat → Bool) (p N₀ : Nat)
    (hbs : ∀ n, n ≥ N₀ → bs (n + p) = bs n) :
    ∀ k n, n ≥ N₀ → bs (n + k * p) = bs n := by
  intro k
  induction k with
  | zero => intro n _; show bs (n + 0 * p) = bs n
            rw [Nat.zero_mul, Nat.add_zero]
  | succ k' ih =>
    intro n hn
    have hext : n + k' * p ≥ N₀ := Nat.le_trans hn (Nat.le_add_right n _)
    rw [Nat.succ_mul, ← Nat.add_assoc, hbs (n + k' * p) hext, ih n hn]

/-- Joint state at offset N₀: (sig (N₀ + k), k mod p) → Fin (5p).
    STRICT ∅-AXIOM. -/
def jointStateAt (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p)
    (k : Fin (5 * p + 1)) : Fin (5 * p) :=
  ⟨(signature bs (N₀ + k.val)).val * p + k.val % p, by
    have h1 : (signature bs (N₀ + k.val)).val < 5 :=
      (signature bs (N₀ + k.val)).isLt
    have h2 : k.val % p < p := Nat.mod_lt _ hp
    have h1' : (signature bs (N₀ + k.val)).val ≤ 4 :=
      Nat.lt_succ_iff.mp h1
    have h3 : (signature bs (N₀ + k.val)).val * p ≤ 4 * p :=
      Nat.mul_le_mul_right p h1'
    calc (signature bs (N₀ + k.val)).val * p + k.val % p
        < 4 * p + p := Nat.add_lt_add_of_le_of_lt h3 h2
      _ = (4 + 1) * p := (Nat.succ_mul 4 p).symm
      _ = 5 * p := rfl⟩

/-- Joint state collision at offset N₀.  STRICT ∅-AXIOM. -/
theorem joint_state_collision_at (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p) :
    ∃ i, i ≤ 5 * p ∧ ∃ j, j ≤ 5 * p ∧ i < j
      ∧ signature bs (N₀ + i) = signature bs (N₀ + j)
      ∧ i % p = j % p := by
  have hlt : 5 * p < 5 * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (jointStateAt bs p N₀ hp)
  have hval_eq : (jointStateAt bs p N₀ hp ⟨i, hi⟩).val
              = (jointStateAt bs p N₀ hp ⟨j, hj⟩).val :=
    collTest_imp_val_eq (jointStateAt bs p N₀ hp) i j hi hj hcoll
  have hval : (signature bs (N₀ + i)).val * p + i % p
              = (signature bs (N₀ + j)).val * p + j % p := hval_eq
  have hmi : i % p < p := Nat.mod_lt _ hp
  have hmj : j % p < p := Nat.mod_lt _ hp
  obtain ⟨h_sig_val_eq, h_mod_eq⟩ :=
    encode_inj hp (signature bs (N₀ + i)).val (signature bs (N₀ + j)).val
      (i % p) (j % p) hmi hmj hval
  exact ⟨i, Nat.lt_succ_iff.mp hi, j, Nat.lt_succ_iff.mp hj, hij,
         Fin.ext h_sig_val_eq, h_mod_eq⟩

/-- ∅-axiom replacement for `Nat.sub_pos_of_lt`. -/
private theorem sub_pos_of_lt_213_local : ∀ {a b : Nat}, a < b → 0 < b - a
  | 0, _, h => by rw [Nat.sub_zero]; exact h
  | _+1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _+1, _+1, h => by
    rw [Nat.succ_sub_succ_eq_sub]
    exact sub_pos_of_lt_213_local (Nat.lt_of_succ_lt_succ h)

/-- ★★★★★ FORWARD direction (eventual): bits eventually periodic
    (period p from N₀) ⇒ signature eventually periodic.  STRICT ∅-AXIOM. -/
theorem signature_eventually_periodic_of_eventually_periodic_bits
    (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p)
    (hbs : ∀ n, n ≥ N₀ → bs (n + p) = bs n) :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N → signature bs (n + P) = signature bs n := by
  obtain ⟨i, _, j, _, hij, hsig, hmod⟩ := joint_state_collision_at bs p N₀ hp
  refine ⟨N₀ + i, j - i, sub_pos_of_lt_213_local hij, ?_⟩
  obtain ⟨k, hk⟩ := sub_is_multiple_of_p i j p hp (Nat.le_of_lt hij) hmod
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = N₀ + i + d :=
    ⟨n - (N₀ + i), (E213.Tactic.NatHelper.add_sub_of_le hn).symm⟩
  clear hn
  have hij_le : i ≤ j := Nat.le_of_lt hij
  have hij_eq : i + (j - i) = j := E213.Tactic.NatHelper.add_sub_of_le hij_le
  have hN_step : N₀ + i + (j - i) = N₀ + j := by
    rw [Nat.add_assoc, hij_eq]
  induction d with
  | zero =>
    show signature bs (N₀ + i + 0 + (j - i)) = signature bs (N₀ + i + 0)
    rw [Nat.add_zero, hN_step]
    exact hsig.symm
  | succ d' ih =>
    have h1 : N₀ + i + (d' + 1) + (j - i)
                = (N₀ + i + d' + (j - i)) + 1 :=
      Nat.succ_add (N₀ + i + d') (j - i)
    have h2 : N₀ + i + (d' + 1) = (N₀ + i + d') + 1 := rfl
    rw [h1, h2]
    show nextVertex (signature bs (N₀ + i + d' + (j - i)))
            (bs (N₀ + i + d' + (j - i)))
      = nextVertex (signature bs (N₀ + i + d')) (bs (N₀ + i + d'))
    rw [ih]
    congr 1
    rw [hk]
    have hext : N₀ + i + d' ≥ N₀ :=
      Nat.le_trans (Nat.le_add_right N₀ i) (Nat.le_add_right (N₀ + i) d')
    exact bs_periodic_multiple_from bs p N₀ hbs k (N₀ + i + d') hext

end E213.Lib.Math.DyadicFSM.Forward.ForwardEventual
