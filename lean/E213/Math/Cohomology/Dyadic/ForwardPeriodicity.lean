import E213.Math.Cohomology.Dyadic.TierBridge
import E213.Math.Pigeonhole

/-!
# Forward direction (general): periodic bits ⇒ ev-periodic signature

Joint state (sig n, n mod p) ∈ Fin (5p); pigeonhole forces a
collision among 5p+1 steps.  Decidable.byContradiction (no
Classical) on Bool-valued `collisionTest` keeps everything at
≤ {propext, Quot.sound}.
-/

namespace E213.Math.Cohomology.Dyadic.ForwardPeriodicity

open E213.Math.Pigeonhole

/-- Bool-valued collision test (decidable, no Classical). -/
def collisionTest {N k : Nat} (g : Fin k → Fin N) (i j : Nat) : Bool :=
  if h_i : i < k then
    if h_j : j < k then (g ⟨i, h_i⟩).val == (g ⟨j, h_j⟩).val
    else false
  else false

/-- Constructive pigeonhole — Decidable extraction (no Classical). -/
theorem pigeonhole_collision {N k : Nat} (h : N < k) (g : Fin k → Fin N) :
    ∃ i, i < k ∧ ∃ j, j < k ∧ i < j ∧ collisionTest g i j = true := by
  apply Decidable.byContradiction
  intro hno
  apply no_inj_lt h g
  intro i j hij heq
  have hi_eq : (⟨i.val, i.isLt⟩ : Fin k) = i := Fin.ext rfl
  have hj_eq : (⟨j.val, j.isLt⟩ : Fin k) = j := Fin.ext rfl
  rcases Nat.lt_or_ge i.val j.val with hlt | hge
  · apply hno
    refine ⟨i.val, i.isLt, j.val, j.isLt, hlt, ?_⟩
    show collisionTest g i.val j.val = true
    unfold collisionTest
    rw [dif_pos i.isLt, dif_pos j.isLt, hi_eq, hj_eq, heq]
    exact beq_iff_eq.mpr rfl
  · rcases Nat.lt_or_eq_of_le hge with hgt | heq_idx
    · apply hno
      refine ⟨j.val, j.isLt, i.val, i.isLt, hgt, ?_⟩
      show collisionTest g j.val i.val = true
      unfold collisionTest
      rw [dif_pos j.isLt, dif_pos i.isLt, hi_eq, hj_eq, heq]
      exact beq_iff_eq.mpr rfl
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
    have h1' : (signature bs k.val).val ≤ 4 := Nat.lt_succ_iff.mp h1
    have h3 : (signature bs k.val).val * p ≤ 4 * p :=
      Nat.mul_le_mul_right p h1'
    calc (signature bs k.val).val * p + k.val % p
        < 4 * p + p := Nat.add_lt_add_of_le_of_lt h3 h2
      _ = (4 + 1) * p := (Nat.succ_mul 4 p).symm
      _ = 5 * p := rfl⟩

/-- ★ Joint state collision: ∃ i < j ≤ 5p with sig & mod equal. -/
theorem joint_state_collision (bs : Nat → Bool) (p : Nat) (hp : 0 < p) :
    ∃ i, i ≤ 5 * p ∧ ∃ j, j ≤ 5 * p ∧ i < j
      ∧ signature bs i = signature bs j
      ∧ i % p = j % p := by
  have hlt : 5 * p < 5 * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (jointState bs p hp)
  have hi' : i ≤ 5 * p := Nat.lt_succ_iff.mp hi
  have hj' : j ≤ 5 * p := Nat.lt_succ_iff.mp hj
  -- collisionTest gives joint state val equal
  have hjs_eq : (jointState bs p hp ⟨i, hi⟩).val
                  = (jointState bs p hp ⟨j, hj⟩).val := by
    unfold collisionTest at hcoll
    simp [hi, hj] at hcoll
    omega
  have hval : (signature bs i).val * p + i % p
                = (signature bs j).val * p + j % p := by
    show (jointState bs p hp ⟨i, hi⟩).val
          = (jointState bs p hp ⟨j, hj⟩).val
    exact hjs_eq
  have hmi : i % p < p := Nat.mod_lt _ hp
  have hmj : j % p < p := Nat.mod_lt _ hp
  have hdiv_i : ((signature bs i).val * p + i % p) / p
                  = (signature bs i).val := by
    rw [Nat.mul_comm (signature bs i).val p, Nat.add_comm,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hmi, Nat.zero_add]
  have hdiv_j : ((signature bs j).val * p + j % p) / p
                  = (signature bs j).val := by
    rw [Nat.mul_comm (signature bs j).val p, Nat.add_comm,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hmj, Nat.zero_add]
  have h_sig_val_eq : (signature bs i).val = (signature bs j).val := by
    rw [← hdiv_i, ← hdiv_j, hval]
  refine ⟨i, hi', j, hj', hij, Fin.ext h_sig_val_eq, ?_⟩
  have h_offset : (signature bs i).val * p = (signature bs j).val * p :=
    by rw [h_sig_val_eq]
  omega

end E213.Math.Cohomology.Dyadic.ForwardPeriodicity
