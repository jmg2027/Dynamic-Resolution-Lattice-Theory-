import E213.Math.Cohomology.Dyadic.ForwardPeriodicity
import E213.Kernel.Tactic.Nat213

/-!
# Forward closure: bits periodic ⇒ signature eventually periodic

Completes the inductive step from `joint_state_collision`.  Combined
with the backward direction (`signature_periodic_implies_bits_periodic`),
this gives the full bidirectional Tier 0 equivalence.

All theorems at ≤ {propext, Quot.sound} (Classical.choice removed).
-/

namespace E213.Math.Cohomology.Dyadic.ForwardClosure

open E213.Math.Cohomology.Dyadic.Signature (signature nextVertex)
open E213.Math.Cohomology.Dyadic.ForwardPeriodicity
  (joint_state_collision bs_periodic_multiple)

/-- If i % p = j % p and i ≤ j, then j - i is a multiple of p. -/
theorem sub_is_multiple_of_p (i j p : Nat) (hp : 0 < p)
    (hij : i ≤ j) (hmod : i % p = j % p) :
    ∃ k, j - i = k * p := by
  refine ⟨(j - i) / p, ?_⟩
  -- First: (j - i) % p = 0 via add_mod on j = i + (j - i)
  have h1 : (j - i) % p = 0 := by
    have h_eq : j % p = (i % p + (j - i) % p) % p := by
      have hadd : (i + (j - i)) % p = (i % p + (j - i) % p) % p :=
        Nat.add_mod i (j - i) p
      rwa [Nat.add_sub_cancel' hij] at hadd
    rw [hmod] at h_eq
    -- h_eq : j % p = (j % p + (j - i) % p) % p
    -- Use bounds: j % p < p, (j - i) % p < p
    have hjlt : j % p < p := Nat.mod_lt _ hp
    have hslt : (j - i) % p < p := Nat.mod_lt _ hp
    -- If j%p + (j-i)%p < p, then mod is the sum, so (j-i)%p = 0.
    -- If ≥ p, then mod is sum - p, so (j-i)%p = p, contradiction.
    by_cases hsum : j % p + (j - i) % p < p
    · rw [Nat.mod_eq_of_lt hsum] at h_eq; omega
    · have hsum' : j % p + (j - i) % p ≥ p := by omega
      have : (j % p + (j - i) % p) % p = j % p + (j - i) % p - p := by
        have hbound : j % p + (j - i) % p < 2 * p := by omega
        have := Nat.mod_eq_sub_mod hsum'
        rw [this]; rw [Nat.mod_eq_of_lt (by omega)]
      rw [this] at h_eq; omega
  have h2 : p * ((j - i) / p) + (j - i) % p = j - i :=
    Nat.div_add_mod (j - i) p
  rw [h1, Nat.add_zero] at h2
  rw [Nat.mul_comm] at h2
  exact h2.symm

/-- ∅-axiom replacement for `Nat.sub_pos_of_lt`. -/
private theorem sub_pos_of_lt_213_local : ∀ {a b : Nat}, a < b → 0 < b - a
  | 0, _, h => by rw [Nat.sub_zero]; exact h
  | _+1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _+1, _+1, h => by
    rw [Nat.succ_sub_succ_eq_sub]
    exact sub_pos_of_lt_213_local (Nat.lt_of_succ_lt_succ h)

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
    ⟨n - i, (E213.Tactic.Nat213.add_sub_of_le hn).symm⟩
  clear hn
  have hij_le : i ≤ j := Nat.le_of_lt hij
  have hij_eq : i + (j - i) = j := E213.Tactic.Nat213.add_sub_of_le hij_le
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

end E213.Math.Cohomology.Dyadic.ForwardClosure
