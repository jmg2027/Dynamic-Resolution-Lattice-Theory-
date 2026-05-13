import E213.Lens.Instances.Leaves.ModNat
import E213.Lens.Cardinality.LensCardinality
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213

/-!
# KernelCardinalityLB: lower bound on the Lens kernel space (≥ ℵ₀)

The `leavesModNat m` family provides distinct kernels for each m,
so the Lens kernel space is **at least countably infinite**.

Combined with the upper bound 𝔠 (Raw is countable so equivalence
relations have 2^(Raw²) = 𝔠): ℵ₀ ≤ |kernel space| ≤ 𝔠.

The exact cardinality is an open conjecture (note 47).  But the
**lower bound is established** by the mod family.

## Main Theorem

`leavesModNat_kernel_neq`: m ≠ k (both ≥ 2) → the kernels
of the two Lenses differ.

∅-axiom version: `omega` and propext-bearing Lean-core Nat lemmas
(`Nat.add_mod_left`, `Nat.add_mod`, `Nat.mod_self`,
`Nat.dvd_of_mod_eq_zero`) replaced with `Gcd213` + `AddMod213` +
manual Nat arithmetic.
-/

namespace E213.Lens.Cardinality.CardinalityLB

open E213.Theory E213.Lens E213.Lens.Instances.Leaves.ModNat
open E213.Meta.Nat.Gcd213 (mod_self_pos mod_zero_dvd)
open E213.Meta.Nat.AddMod213 (add_mod_gen)

/-- `(a + b) % a = b % a` when `0 < a`.  ∅-axiom. -/
private theorem add_mod_left_pos (a b : Nat) (ha : 0 < a) :
    (a + b) % a = b % a := by
  rw [add_mod_gen, mod_self_pos a ha, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Nat.mod_lt b ha)

/-- If m ≠ k (both ≥ 2) then the kernel of leavesModNat m ≠
    the kernel of leavesModNat k.  ∅-axiom. -/
private theorem mod_kernel_separates (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hnotdvd : ¬ k ∣ m) :
    ∃ r r' : Raw,
      (leavesModNat m).view r = (leavesModNat m).view r' ∧
      (leavesModNat k).view r ≠ (leavesModNat k).view r' := by
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hm
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hk
  have hm_p1_pos : 0 < m + 1 := Nat.zero_lt_succ m
  obtain ⟨r', hr'⟩ := E213.Lens.Cardinality.leaves_surjective_pos (m + 1) hm_p1_pos
  refine ⟨Raw.a, r', ?_, ?_⟩
  · -- 1 % m = (m+1) % m
    show (leavesModNat m).view Raw.a = (leavesModNat m).view r'
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hr']
    show 1 % m = (m + 1) % m
    exact (add_mod_left_pos m 1 hm_pos).symm
  · -- 1 % k ≠ (m+1) % k
    show (leavesModNat k).view Raw.a ≠ (leavesModNat k).view r'
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hr']
    show 1 % k ≠ (m + 1) % k
    rw [Nat.mod_eq_of_lt (show (1 : Nat) < k from hk)]
    -- m % k > 0 (else k ∣ m)
    have h_mk_pos : 0 < m % k := by
      match h_eq : m % k with
      | 0 =>
        exfalso
        exact hnotdvd (mod_zero_dvd m m k hk_pos (Nat.le_refl m) h_eq)
      | n+1 => exact Nat.zero_lt_succ n
    have h_mk_lt : m % k < k := Nat.mod_lt _ hk_pos
    -- (m+1) % k = (m % k + 1) % k
    have hstep : (m + 1) % k = (m % k + 1) % k := by
      rw [add_mod_gen]
      rw [Nat.mod_eq_of_lt (show (1 : Nat) < k from hk)]
    rw [hstep]
    -- Case split: m % k + 1 < k vs ≥ k
    by_cases hcase : m % k + 1 < k
    · -- (m%k + 1) % k = m%k + 1, which is ≥ 2 > 1
      rw [Nat.mod_eq_of_lt hcase]
      -- 1 ≠ m % k + 1.  Have m % k > 0, so m % k + 1 ≥ 2 > 1.
      intro hcontra
      -- hcontra : 1 = m % k + 1.  1 = (m%k).succ → 0 = m%k
      have h_eq : m % k = 0 := by
        have h_succ : (0 : Nat).succ = (m % k).succ := hcontra
        exact (Nat.succ.inj h_succ).symm
      rw [h_eq] at h_mk_pos
      exact absurd h_mk_pos (Nat.lt_irrefl 0)
    · -- m % k + 1 ≥ k.  And m % k < k → m % k + 1 ≤ k.  So m % k + 1 = k.
      have h_le : m % k + 1 ≤ k := h_mk_lt
      have h_ge : k ≤ m % k + 1 := Nat.le_of_not_lt hcase
      have heq : m % k + 1 = k := Nat.le_antisymm h_le h_ge
      rw [heq, mod_self_pos k hk_pos]
      decide

end E213.Lens.Cardinality.CardinalityLB

namespace E213.Lens.Cardinality.CardinalityLB

open E213.Theory E213.Lens E213.Lens.Instances.Leaves.ModNat

/-- **Distinct mod kernels for distinct moduli (m ≠ k, both ≥ 2)**.
    ∅-axiom. -/
theorem leavesModNat_kernel_neq (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hne : m ≠ k) :
    ∃ r r' : Raw,
      ¬ ((leavesModNat m).view r = (leavesModNat m).view r' ↔
          (leavesModNat k).view r = (leavesModNat k).view r') := by
  rcases Nat.lt_or_ge m k with hlt | hge
  · -- m < k, so k ∤ m (k > m ≥ 2 > 0).
    have hnotdvd : ¬ k ∣ m := by
      intro ⟨q, hq⟩
      cases q with
      | zero =>
        rw [Nat.mul_zero] at hq
        rw [hq] at hm
        exact absurd hm (by decide)
      | succ n =>
        have h_kn1 : k * 1 ≤ k * (n + 1) :=
          Nat.mul_le_mul_left k (Nat.succ_le_succ (Nat.zero_le _))
        rw [Nat.mul_one] at h_kn1
        have h_k_le_m : k ≤ m := by
          have h1 : k * (n + 1) = m := hq.symm
          exact h1 ▸ h_kn1
        exact absurd h_k_le_m (Nat.not_le_of_lt hlt)
    obtain ⟨r, r', heqm, hneqk⟩ := mod_kernel_separates m k hm hk hnotdvd
    exact ⟨r, r', fun h => hneqk (h.mp heqm)⟩
  · -- m ≥ k.  m > k since m ≠ k.
    have hgt : m > k := Nat.lt_of_le_of_ne hge (Ne.symm hne)
    have hnotdvd : ¬ m ∣ k := by
      intro ⟨q, hq⟩
      cases q with
      | zero =>
        rw [Nat.mul_zero] at hq
        rw [hq] at hk
        exact absurd hk (by decide)
      | succ n =>
        have h_mn1 : m * 1 ≤ m * (n + 1) :=
          Nat.mul_le_mul_left m (Nat.succ_le_succ (Nat.zero_le _))
        rw [Nat.mul_one] at h_mn1
        have h_m_le_k : m ≤ k := by
          have h1 : m * (n + 1) = k := hq.symm
          exact h1 ▸ h_mn1
        exact absurd h_m_le_k (Nat.not_le_of_lt hgt)
    obtain ⟨r, r', heqk, hneqm⟩ := mod_kernel_separates k m hk hm hnotdvd
    exact ⟨r, r', fun h => hneqm (h.mpr heqk)⟩

end E213.Lens.Cardinality.CardinalityLB
