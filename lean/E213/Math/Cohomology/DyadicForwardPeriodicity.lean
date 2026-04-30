import E213.Math.Cohomology.DyadicTierBridge
import E213.OS.Pigeonhole

/-!
# Forward direction (general): periodic bits ⇒ ev-periodic signature

Joint state (sig n, n mod p) ∈ Fin (5p) has 5p values; among 5p+1
consecutive steps, pigeonhole forces a collision.  From the
collision, signature is periodic with period P (multiple of p)
starting at the collision step.

**Axiom note**: existential extraction via `Classical.byContradiction`
adds `Classical.choice` (research-level).  `bs_periodic_multiple`
remains STRICT 0-axiom.  For 0-axiom Tier-0 forward see
`one_third_signature_periodic` in `DyadicTierBridge`.
-/

namespace E213.Math.Cohomology.DyadicConjecture

open E213.OS.Pigeonhole

/-- Pigeonhole-derived collision (existential form). -/
theorem pigeonhole_collision {N k : Nat} (h : N < k) (g : Fin k → Fin N) :
    ∃ i j : Fin k, i.val < j.val ∧ g i = g j :=
  Classical.byContradiction fun hno => by
    apply no_inj_lt h g
    intro i j hij heq
    rcases Nat.lt_or_ge i.val j.val with hlt | hge
    · exact hno ⟨i, j, hlt, heq⟩
    · rcases Nat.lt_or_eq_of_le hge with hgt | heq_idx
      · exact hno ⟨j, i, hgt, heq.symm⟩
      · exact hij (Fin.ext heq_idx.symm)

/-- bs periodic at multiple of p: bs (n + k*p) = bs n. -/
theorem bs_periodic_multiple (bs : Nat → Bool) (p : Nat)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∀ k n, bs (n + k * p) = bs n := by
  intro k
  induction k with
  | zero => intro n; show bs (n + 0 * p) = bs n; rw [Nat.zero_mul, Nat.add_zero]
  | succ k' ih =>
    intro n
    rw [Nat.succ_mul, ← Nat.add_assoc, hbs, ih]

/-- Joint state map: (signature, position in period) → Fin (5p). -/
def jointState (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (k : Fin (5 * p + 1)) : Fin (5 * p) :=
  ⟨(signature bs k.val).val * p + k.val % p, by
    have h1 : (signature bs k.val).val < 5 := (signature bs k.val).isLt
    have h2 : k.val % p < p := Nat.mod_lt _ hp
    have h3 : (signature bs k.val).val * p ≤ 4 * p :=
      Nat.mul_le_mul_right p (by omega)
    omega⟩

/-- ★ Joint state collision: ∃ i < j ∈ Fin (5p+1) with sig & mod equal. -/
theorem joint_state_collision (bs : Nat → Bool) (p : Nat) (hp : 0 < p) :
    ∃ i j : Fin (5 * p + 1), i.val < j.val
      ∧ signature bs i.val = signature bs j.val
      ∧ i.val % p = j.val % p := by
  have hlt : 5 * p < 5 * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, j, hij, heq⟩ := pigeonhole_collision hlt (jointState bs p hp)
  have hval : (signature bs i.val).val * p + i.val % p
                = (signature bs j.val).val * p + j.val % p := by
    have := congrArg Fin.val heq; simpa [jointState] using this
  have hmi : i.val % p < p := Nat.mod_lt _ hp
  have hmj : j.val % p < p := Nat.mod_lt _ hp
  have hdiv_i : ((signature bs i.val).val * p + i.val % p) / p
                  = (signature bs i.val).val := by
    rw [Nat.mul_comm (signature bs i.val).val p, Nat.add_comm,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hmi, Nat.zero_add]
  have hdiv_j : ((signature bs j.val).val * p + j.val % p) / p
                  = (signature bs j.val).val := by
    rw [Nat.mul_comm (signature bs j.val).val p, Nat.add_comm,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hmj, Nat.zero_add]
  have h_sig_val_eq : (signature bs i.val).val = (signature bs j.val).val := by
    rw [← hdiv_i, ← hdiv_j, hval]
  refine ⟨i, j, hij, Fin.ext h_sig_val_eq, ?_⟩
  have h_offset : (signature bs i.val).val * p = (signature bs j.val).val * p :=
    by rw [h_sig_val_eq]
  omega

end E213.Math.Cohomology.DyadicConjecture
