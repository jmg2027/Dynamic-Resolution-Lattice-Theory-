import E213.Math.Cohomology.DyadicForwardPeriodicity

/-!
# Forward closure: bits periodic ⇒ signature eventually periodic

Completes the inductive step from `joint_state_collision`.  Combined
with the backward direction (`signature_periodic_implies_bits_periodic`),
this gives the full bidirectional Tier 0 equivalence.

All theorems at ≤ {propext, Quot.sound} (Classical.choice removed).
-/

namespace E213.Math.Cohomology.DyadicConjecture

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

/-- ★★★ Forward direction: bits periodic ⇒ signature eventually periodic. -/
theorem signature_eventually_periodic_of_periodic_bits
    (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N → signature bs (n + P) = signature bs n := by
  obtain ⟨i, _, j, _, hij, hsig, hmod⟩ := joint_state_collision bs p hp
  refine ⟨i, j - i, by omega, ?_⟩
  obtain ⟨k, hk⟩ := sub_is_multiple_of_p i j p hp (Nat.le_of_lt hij) hmod
  intro n hn
  -- Induction on (n - i)
  obtain ⟨d, rfl⟩ : ∃ d, n = i + d := ⟨n - i, (Nat.add_sub_cancel' hn).symm⟩
  clear hn
  induction d with
  | zero =>
    show signature bs (i + 0 + (j - i)) = signature bs (i + 0)
    rw [Nat.add_zero, Nat.add_comm i (j - i), Nat.sub_add_cancel (Nat.le_of_lt hij)]
    exact hsig.symm
  | succ d' ih =>
    show signature bs (i + (d' + 1) + (j - i)) = signature bs (i + (d' + 1))
    have h1 : signature bs (i + (d' + 1) + (j - i))
                = nextVertex (signature bs (i + d' + (j - i)))
                    (bs (i + d' + (j - i))) := by
      have hidx : i + (d' + 1) + (j - i) = (i + d' + (j - i)) + 1 := by omega
      rw [hidx]; rfl
    have h2 : signature bs (i + (d' + 1))
                = nextVertex (signature bs (i + d')) (bs (i + d')) := by
      show signature bs (i + d' + 1)
            = nextVertex (signature bs (i + d')) (bs (i + d'))
      rfl
    rw [h1, h2, ih]
    congr 1
    rw [hk]
    exact bs_periodic_multiple bs p hbs k (i + d')

end E213.Math.Cohomology.DyadicConjecture
