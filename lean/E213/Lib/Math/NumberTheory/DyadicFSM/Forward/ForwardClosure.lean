import E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardPeriodicity
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.AddMod213

import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature
/-!
# Forward closure: bits periodic ⇒ signature eventually periodic

Completes the inductive step from `joint_state_collision`.  Combined
with the backward direction (`signature_periodic_implies_bits_periodic`),
this gives the full bidirectional Tier 0 equivalence.

All theorems are PURE (∅-axiom) (Classical.choice removed).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardClosure

open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature nextVertex)
open E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardPeriodicity
  (joint_state_collision bs_periodic_multiple)

/-- Helper: if `c ≤ a` and `a < b + c`, then `a - c < b`.  ∅-axiom. -/
private theorem sub_lt_of_lt_add {a b c : Nat} (hca : c ≤ a)
    (h : a < b + c) : a - c < b := by
  have h1 : a - c + c = a := E213.Tactic.NatHelper.sub_add_cancel hca
  exact Nat.lt_of_add_lt_add_right (h1.symm ▸ h)

/-- If i % p = j % p and i ≤ j, then j - i is a multiple of p.
    STRICT ∅-AXIOM via 213-native add_mod / div_add_mod helpers. -/
theorem sub_is_multiple_of_p (i j p : Nat) (hp : 0 < p)
    (hij : i ≤ j) (hmod : i % p = j % p) :
    ∃ k, j - i = k * p := by
  refine ⟨(j - i) / p, ?_⟩
  have hjlt : j % p < p := Nat.mod_lt _ hp
  have hslt : (j - i) % p < p := Nat.mod_lt _ hp
  have h1 : (j - i) % p = 0 := by
    have hji : i + (j - i) = j := E213.Tactic.NatHelper.add_sub_of_le hij
    have hadd : j % p = (i % p + (j - i)) % p := by
      have h := E213.Meta.Nat.AddMod213.add_mod_left hp i (j - i)
      rw [hji] at h
      exact h
    rw [hmod] at hadd
    have hadd2 : (j % p + (j - i)) % p
                = (j % p % p + (j - i) % p) % p :=
      E213.Meta.Nat.AddMod213.add_mod hp _ _
    rw [E213.Meta.Nat.AddMod213.mod_mod] at hadd2
    rw [hadd2] at hadd
    -- hadd : j % p = (j % p + (j - i) % p) % p
    by_cases hsum : j % p + (j - i) % p < p
    · -- (j-i)%p = 0 directly
      rw [Nat.mod_eq_of_lt hsum] at hadd
      have h0 : j % p + 0 = j % p := Nat.add_zero _
      exact (E213.Tactic.NatHelper.add_left_cancel
              (h0.trans hadd)).symm
    · exfalso
      have hsum_ge : p ≤ j % p + (j - i) % p := Nat.le_of_not_lt hsum
      have hsum_p_p : j % p + (j - i) % p < p + p :=
        Nat.add_lt_add hjlt hslt
      have hsum_minus_lt : j % p + (j - i) % p - p < p :=
        sub_lt_of_lt_add hsum_ge hsum_p_p
      have hmod_sub : (j % p + (j - i) % p) % p
                    = j % p + (j - i) % p - p := by
        rw [Nat.mod_eq_sub_mod hsum_ge]
        exact Nat.mod_eq_of_lt hsum_minus_lt
      rw [hmod_sub] at hadd
      -- hadd : j%p = j%p + (j-i)%p - p
      have h_add_p : j % p + p = j % p + (j - i) % p :=
        (congrArg (· + p) hadd).trans
          (E213.Tactic.NatHelper.sub_add_cancel hsum_ge)
      have h_p_eq : p = (j - i) % p :=
        E213.Tactic.NatHelper.add_left_cancel h_add_p
      -- hslt : (j-i)%p < p; want: False
      -- Use Nat.lt_irrefl with: (j-i)%p < (j-i)%p (rewriting p → (j-i)%p in hslt's RHS)
      have hcontra : (j - i) % p < (j - i) % p := h_p_eq ▸ hslt
      exact Nat.lt_irrefl _ hcontra
  have h2 : p * ((j - i) / p) + (j - i) % p = j - i :=
    E213.Meta.Nat.AddMod213.div_add_mod (j - i) p
  rw [h1, Nat.add_zero] at h2
  rw [Nat.mul_comm] at h2
  exact h2.symm

open E213.Tactic.NatHelper renaming sub_pos_of_lt → sub_pos_of_lt_213_local

/-- ★★★ Forward direction: bits periodic ⇒ signature eventually periodic.
    STRICT ∅-AXIOM. -/
theorem signature_eventually_periodic_of_periodic_bits
    (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N → signature bs (n + P) = signature bs n := by
  obtain ⟨i, _, j, _, hij, hsig, hmod⟩ := joint_state_collision bs p hp
  refine ⟨i, j - i, sub_pos_of_lt_213_local hij, ?_⟩
  obtain ⟨k, hk⟩ := sub_is_multiple_of_p i j p hp (Nat.le_of_lt hij) hmod
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = i + d :=
    ⟨n - i, (E213.Tactic.NatHelper.add_sub_of_le hn).symm⟩
  clear hn
  have hij_le : i ≤ j := Nat.le_of_lt hij
  have hij_eq : i + (j - i) = j := E213.Tactic.NatHelper.add_sub_of_le hij_le
  induction d with
  | zero =>
    show signature bs (i + 0 + (j - i)) = signature bs (i + 0)
    rw [Nat.add_zero, hij_eq]
    exact hsig.symm
  | succ d' ih =>
    show signature bs (i + (d' + 1) + (j - i)) = signature bs (i + (d' + 1))
    have hidx : i + (d' + 1) + (j - i) = (i + d' + (j - i)) + 1 :=
      Nat.succ_add (i + d') (j - i)
    have h1 : signature bs (i + (d' + 1) + (j - i))
                = nextVertex (signature bs (i + d' + (j - i)))
                    (bs (i + d' + (j - i))) := by rw [hidx]; rfl
    have h2 : signature bs (i + (d' + 1))
                = nextVertex (signature bs (i + d')) (bs (i + d')) := rfl
    rw [h1, h2, ih]
    congr 1
    rw [hk]
    exact bs_periodic_multiple bs p hbs k (i + d')

end E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardClosure
