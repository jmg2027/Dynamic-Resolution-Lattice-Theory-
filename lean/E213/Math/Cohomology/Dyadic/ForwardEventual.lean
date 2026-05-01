import E213.Math.Cohomology.Dyadic.ForwardClosure

/-!
# Forward direction (eventual): eventually periodic bits ⇒
  eventually periodic signature

Strict generalisation of `signature_eventually_periodic_of_periodic_bits`:
the bit stream may have a *pre-period* `N₀` before becoming periodic.

Proof structure mirrors the purely-periodic case but with offset:
joint state (sig (N₀ + k), k mod p) over k ∈ Fin (5p+1) collides
by pigeonhole; periodicity follows from N₀ + i onwards.

All theorems at ≤ {propext, Quot.sound}.
-/

namespace E213.Math.Cohomology.Dyadic.ForwardEventual

/-- bs eventually periodic at multiple of p, from N₀ onwards. -/
theorem bs_periodic_multiple_from (bs : Nat → Bool) (p N₀ : Nat)
    (hbs : ∀ n, n ≥ N₀ → bs (n + p) = bs n) :
    ∀ k n, n ≥ N₀ → bs (n + k * p) = bs n := by
  intro k
  induction k with
  | zero => intro n _; show bs (n + 0 * p) = bs n
            rw [Nat.zero_mul, Nat.add_zero]
  | succ k' ih =>
    intro n hn
    rw [Nat.succ_mul, ← Nat.add_assoc, hbs (n + k' * p) (by omega), ih n hn]

/-- Joint state at offset N₀: (sig (N₀ + k), k mod p) → Fin (5p). -/
def jointStateAt (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p)
    (k : Fin (5 * p + 1)) : Fin (5 * p) :=
  ⟨(signature bs (N₀ + k.val)).val * p + k.val % p, by
    have h1 : (signature bs (N₀ + k.val)).val < 5 :=
      (signature bs (N₀ + k.val)).isLt
    have h2 : k.val % p < p := Nat.mod_lt _ hp
    have h3 : (signature bs (N₀ + k.val)).val * p ≤ 4 * p :=
      Nat.mul_le_mul_right p (by omega)
    omega⟩

/-- Joint state collision at offset N₀. -/
theorem joint_state_collision_at (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p) :
    ∃ i, i ≤ 5 * p ∧ ∃ j, j ≤ 5 * p ∧ i < j
      ∧ signature bs (N₀ + i) = signature bs (N₀ + j)
      ∧ i % p = j % p := by
  have hlt : 5 * p < 5 * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (jointStateAt bs p N₀ hp)
  have hjs_eq : (jointStateAt bs p N₀ hp ⟨i, hi⟩).val
                  = (jointStateAt bs p N₀ hp ⟨j, hj⟩).val := by
    unfold collisionTest at hcoll
    simp [hi, hj] at hcoll
    omega
  have hval : (signature bs (N₀ + i)).val * p + i % p
                = (signature bs (N₀ + j)).val * p + j % p :=
    hjs_eq
  have hmi : i % p < p := Nat.mod_lt _ hp
  have hmj : j % p < p := Nat.mod_lt _ hp
  have hdiv_i : ((signature bs (N₀ + i)).val * p + i % p) / p
                  = (signature bs (N₀ + i)).val := by
    rw [Nat.mul_comm (signature bs (N₀ + i)).val p, Nat.add_comm,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hmi, Nat.zero_add]
  have hdiv_j : ((signature bs (N₀ + j)).val * p + j % p) / p
                  = (signature bs (N₀ + j)).val := by
    rw [Nat.mul_comm (signature bs (N₀ + j)).val p, Nat.add_comm,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hmj, Nat.zero_add]
  have h_sig_val_eq : (signature bs (N₀ + i)).val
                        = (signature bs (N₀ + j)).val := by
    rw [← hdiv_i, ← hdiv_j, hval]
  refine ⟨i, by omega, j, by omega, hij, Fin.ext h_sig_val_eq, ?_⟩
  have h_offset : (signature bs (N₀ + i)).val * p
                    = (signature bs (N₀ + j)).val * p := by rw [h_sig_val_eq]
  omega

/-- ★★★★★ FORWARD direction (eventual): bits eventually periodic
    (period p from N₀) ⇒ signature eventually periodic. -/
theorem signature_eventually_periodic_of_eventually_periodic_bits
    (bs : Nat → Bool) (p N₀ : Nat) (hp : 0 < p)
    (hbs : ∀ n, n ≥ N₀ → bs (n + p) = bs n) :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N → signature bs (n + P) = signature bs n := by
  obtain ⟨i, _, j, _, hij, hsig, hmod⟩ := joint_state_collision_at bs p N₀ hp
  refine ⟨N₀ + i, j - i, by omega, ?_⟩
  obtain ⟨k, hk⟩ := sub_is_multiple_of_p i j p hp (Nat.le_of_lt hij) hmod
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = N₀ + i + d :=
    ⟨n - (N₀ + i), (Nat.add_sub_cancel' hn).symm⟩
  clear hn
  induction d with
  | zero =>
    show signature bs (N₀ + i + 0 + (j - i)) = signature bs (N₀ + i + 0)
    rw [Nat.add_zero, show N₀ + i + (j - i) = N₀ + j by omega]
    exact hsig.symm
  | succ d' ih =>
    have h1 : N₀ + i + (d' + 1) + (j - i)
                = (N₀ + i + d' + (j - i)) + 1 := by omega
    have h2 : N₀ + i + (d' + 1) = (N₀ + i + d') + 1 := by omega
    rw [h1, h2]
    show nextVertex (signature bs (N₀ + i + d' + (j - i)))
            (bs (N₀ + i + d' + (j - i)))
      = nextVertex (signature bs (N₀ + i + d')) (bs (N₀ + i + d'))
    rw [ih]
    congr 1
    rw [hk]
    exact bs_periodic_multiple_from bs p N₀ hbs k (N₀ + i + d') (by omega)

end E213.Math.Cohomology.Dyadic.ForwardEventual
