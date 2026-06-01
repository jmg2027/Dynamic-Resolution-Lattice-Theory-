import E213.Lens.LensCore
import E213.Lib.Math.ModArith.JoinGCD
import E213.Meta.Nat.NatDiv213

/-!
# ModJoinEquivGCD: L_gcd.equiv ⊆ JoinEquiv L_m L_k

The **converse direction** of `ModJoinGCD.joinEquiv_subset_gcd`.
Together they establish **L_gcd.equiv = JoinEquiv L_m L_k** —
that is, **L_gcd is the concrete Lens realization of JoinEquiv**
(for the mod family).

Uses the 213-native `gcd213` (∅-axiom).
-/

namespace E213.Lib.Math.ModArith.JoinEquivGCD

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat E213.Lens.Lattice.JoinEquiv
open E213.Lib.Math.ModArith.JoinGCD
open E213.Tactic.NatHelper (gcd213 sub_add_cancel)
open E213.Meta.Nat.Gcd213
  (gcd213_self gcd213_comm gcd213_sub_left mod_eq_exists_mul_add
   succ_sub_self_213)
open E213.Meta.Nat.NatDiv213 (add_mod_right_pos)

open E213.Lens renaming leaves_view_pos → leaves_ge_one_local

/-- **Chain step** at JE level: m > k ≥ 2,
    `leaves r' = leaves r + (m - k) → JoinEquiv L_m L_k r r'`.  ∅-axiom. -/
theorem chain_step_sub_JE (m k : Nat) (hk : k ≥ 2) (hmk : m > k)
    (r r' : Raw) (hdiff : Lens.leaves.view r' = Lens.leaves.view r + (m - k)) :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  have h_pos : 1 ≤ Lens.leaves.view r + m :=
    Nat.le_trans (leaves_ge_one_local r) (Nat.le_add_right _ _)
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hk
  have hm_pos : 0 < m := Nat.lt_trans hk_pos hmk
  obtain ⟨w, hw⟩ := E213.Lens.Cardinality.leaves_surjective_pos
    (Lens.leaves.view r + m) h_pos
  have h_rw_m : (leavesModNat m).equiv r w := by
    show (leavesModNat m).view r = (leavesModNat m).view w
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw,
        add_mod_right_pos hm_pos]
  have h_wr'_k : (leavesModNat k).equiv w r' := by
    show (leavesModNat k).view w = (leavesModNat k).view r'
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    have hkm_le : k ≤ m := Nat.le_of_lt hmk
    have h_sub_add : (m - k) + k = m := sub_add_cancel hkm_le
    have hrewrite : Lens.leaves.view r + m
                      = (Lens.leaves.view r + (m - k)) + k := by
      rw [Nat.add_assoc, h_sub_add]
    rw [hrewrite, add_mod_right_pos hk_pos]
  exact JoinEquiv.trans (JoinEquiv.ofL h_rw_m) (JoinEquiv.ofM h_wr'_k)

/-- **Same leaves** → JoinEquiv via ofL.  ∅-axiom. -/
theorem same_leaves_JE (m k : Nat)
    (r r' : Raw) (hr : Lens.leaves.view r = Lens.leaves.view r') :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  apply JoinEquiv.ofL
  show (leavesModNat m).view r = (leavesModNat m).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

/-- **+n(m-k) chain** at JE level.  ∅-axiom. -/
theorem step_plus_nd_JE (m k : Nat) (hk : k ≥ 2) (hmk : m > k)
    (r : Raw) (n : Nat) :
    ∀ r', Lens.leaves.view r' = Lens.leaves.view r + n * (m - k) →
        JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  induction n with
  | zero =>
      intro r' hr'
      apply same_leaves_JE m k
      rw [Nat.zero_mul, Nat.add_zero] at hr'
      exact hr'.symm
  | succ n ih =>
      intro r' hr'
      have h_bound : 1 ≤ Lens.leaves.view r + n * (m - k) :=
        Nat.le_trans (leaves_ge_one_local r) (Nat.le_add_right _ _)
      obtain ⟨r'', hr''⟩ :=
        E213.Lens.Cardinality.leaves_surjective_pos
          (Lens.leaves.view r + n * (m - k)) h_bound
      have step1 : JoinEquiv (leavesModNat m) (leavesModNat k) r r'' :=
        ih r'' hr''
      have hexpand : (n + 1) * (m - k) = n * (m - k) + (m - k) :=
        Nat.succ_mul n (m - k)
      have step2 : JoinEquiv (leavesModNat m) (leavesModNat k) r'' r' := by
        apply chain_step_sub_JE m k hk hmk r'' r'
        rw [hr', hexpand, ← Nat.add_assoc, ← hr'']
      exact JoinEquiv.trans step1 step2

/-- **Euclidean step** at JE level: L_{m-k}.equiv r r' →
    JoinEquiv L_m L_k r r'.  ∅-axiom. -/
theorem euclidean_step_JE (m k : Nat)
    (hk : k ≥ 2) (hmk : m > k) (hdiff : m - k ≥ 2)
    (r r' : Raw) (h_equiv : (leavesModNat (m - k)).equiv r r') :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  have h_mod : Lens.leaves.view r % (m - k)
                 = Lens.leaves.view r' % (m - k) := by
    have : (leavesModNat (m - k)).view r
             = (leavesModNat (m - k)).view r' := h_equiv
    rw [leavesModNat_view_eq, leavesModNat_view_eq] at this
    exact this
  have hd_pos : 0 < m - k :=
    Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hdiff
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · obtain ⟨q, hq⟩ := mod_eq_exists_mul_add
      (Lens.leaves.view r') (Lens.leaves.view r) (m - k) hd_pos hle h_mod.symm
    exact step_plus_nd_JE m k hk hmk r q r' hq
  · obtain ⟨q, hq⟩ := mod_eq_exists_mul_add
      (Lens.leaves.view r) (Lens.leaves.view r') (m - k) hd_pos hle h_mod
    exact JoinEquiv.symm (step_plus_nd_JE m k hk hmk r' q r hq)

/-- **Consecutive** at JE level. ∅-axiom. -/
theorem consecutive_refines_all_JE (m k : Nat) (hk : k ≥ 2) (hms : m = k + 1) :
    ∀ r r' : Raw, JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  intro r r'
  have hmk : m > k := by rw [hms]; exact Nat.lt_succ_self k
  have hdiff : m - k = 1 := by rw [hms]; exact succ_sub_self_213 k
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · apply step_plus_nd_JE m k hk hmk r (Lens.leaves.view r' - Lens.leaves.view r) r'
    rw [hdiff, Nat.mul_one]
    rw [Nat.add_comm]
    exact (sub_add_cancel hle).symm
  · apply JoinEquiv.symm
    apply step_plus_nd_JE m k hk hmk r' (Lens.leaves.view r - Lens.leaves.view r') r
    rw [hdiff, Nat.mul_one]
    rw [Nat.add_comm]
    exact (sub_add_cancel hle).symm

/-- **Lifting**: JoinEquiv L_{m-k} L_k → JoinEquiv L_m L_k.  ∅-axiom. -/
theorem lift_sub_JE (m k : Nat) (hk : k ≥ 2) (hmk : m > k) (hd : m - k ≥ 2)
    (r r' : Raw)
    (h : JoinEquiv (leavesModNat (m - k)) (leavesModNat k) r r') :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  induction h with
  | ofL h => exact euclidean_step_JE m k hk hmk hd _ _ h
  | ofM h => exact JoinEquiv.ofM h
  | refl x => exact JoinEquiv.refl x
  | symm _ ih => exact JoinEquiv.symm ih
  | trans _ _ ih1 ih2 => exact JoinEquiv.trans ih1 ih2
  | slash_cong hxy hx'y' _ _ ih1 ih2 =>
      exact JoinEquiv.slash_cong hxy hx'y' ih1 ih2

/-- **Swap**: JoinEquiv L_m L_k ↔ JoinEquiv L_k L_m.  ∅-axiom. -/
theorem swap_JE (m k : Nat) (r r' : Raw)
    (h : JoinEquiv (leavesModNat m) (leavesModNat k) r r') :
    JoinEquiv (leavesModNat k) (leavesModNat m) r r' := by
  induction h with
  | ofL h => exact JoinEquiv.ofM h
  | ofM h => exact JoinEquiv.ofL h
  | refl x => exact JoinEquiv.refl x
  | symm _ ih => exact JoinEquiv.symm ih
  | trans _ _ ih1 ih2 => exact JoinEquiv.trans ih1 ih2
  | slash_cong hxy hx'y' _ _ ih1 ih2 =>
      exact JoinEquiv.slash_cong hxy hx'y' ih1 ih2

/-- **Main theorem (sorted)**: strong induction on m + k, m ≥ k assumed.
    L_{gcd213 m k}.equiv → JoinEquiv L_m L_k.  ∅-axiom. -/
private theorem join_eq_gcd_JE_sorted :
    ∀ (s m k : Nat), m + k ≤ s → m ≥ k → m ≥ 2 → k ≥ 2 →
    ∀ r r' : Raw, (leavesModNat (gcd213 m k)).equiv r r' →
      JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  intro s
  induction s with
  | zero =>
      intro m k hsum _ hm _ _ _ _
      exfalso
      have hm_le : m ≤ 0 := Nat.le_trans (Nat.le_add_right _ _) hsum
      have hm_zero : m = 0 := Nat.le_zero.mp hm_le
      rw [hm_zero] at hm
      exact absurd hm (by decide)
  | succ n ih =>
      intro m k hsum hmk hm hk r r' hrr'
      by_cases heq : m = k
      · apply JoinEquiv.ofL
        rw [heq] at hrr'
        rw [gcd213_self] at hrr'
        rw [heq]
        exact hrr'
      · have hmgt : m > k := Nat.lt_of_le_of_ne hmk (Ne.symm heq)
        by_cases hd1 : m - k = 1
        · have hms : m = k + 1 := by
            have h_sub_add : (m - k) + k = m := sub_add_cancel hmk
            rw [hd1, Nat.add_comm] at h_sub_add
            exact h_sub_add.symm
          exact consecutive_refines_all_JE m k hk hms r r'
        · have hd2 : m - k ≥ 2 := by
            match h_eq : m - k with
            | 0 =>
              exfalso
              exact absurd (Nat.le_of_sub_eq_zero h_eq) (Nat.not_le_of_lt hmgt)
            | 1 => exact absurd h_eq hd1
            | n+2 => exact Nat.le_add_left 2 n
          have hrec_hyp : (leavesModNat (gcd213 (m - k) k)).equiv r r' := by
            have hgcd_eq : gcd213 (m - k) k = gcd213 m k :=
              (gcd213_sub_left m k hmk).symm
            show (leavesModNat (gcd213 (m - k) k)).view r
                 = (leavesModNat (gcd213 (m - k) k)).view r'
            rw [hgcd_eq]
            exact hrr'
          have h_m_le_n : m ≤ n := by
            have h1 : m + 2 ≤ m + k := Nat.add_le_add_left hk m
            have h2 : m + 2 ≤ n + 1 := Nat.le_trans h1 hsum
            have h3 : m + 1 ≤ n := Nat.le_of_succ_le_succ h2
            exact Nat.le_trans (Nat.le_succ m) h3
          have h_mk_sum : (m - k) + k ≤ n := by
            rw [sub_add_cancel hmk]; exact h_m_le_n
          by_cases hmkge : m - k ≥ k
          · have hrec : JoinEquiv (leavesModNat (m - k)) (leavesModNat k) r r' :=
              ih (m - k) k h_mk_sum hmkge hd2 hk r r' hrec_hyp
            exact lift_sub_JE m k hk hmgt hd2 r r' hrec
          · have hklt : k > m - k := Nat.lt_of_not_le hmkge
            have hrec_swap : (leavesModNat (gcd213 k (m - k))).equiv r r' := by
              show (leavesModNat (gcd213 k (m - k))).view r
                   = (leavesModNat (gcd213 k (m - k))).view r'
              rw [gcd213_comm]
              exact hrec_hyp
            have h_km_sum : k + (m - k) ≤ n := by
              rw [Nat.add_comm]; exact h_mk_sum
            have hrec : JoinEquiv (leavesModNat k) (leavesModNat (m - k)) r r' :=
              ih k (m - k) h_km_sum (Nat.le_of_lt hklt) hk hd2 r r' hrec_swap
            have hrec' : JoinEquiv (leavesModNat (m - k)) (leavesModNat k) r r' :=
              swap_JE k (m - k) r r' hrec
            exact lift_sub_JE m k hk hmgt hd2 r r' hrec'

/-- **Main theorem at JE level**: L_{gcd213 m k}.equiv r r' → JoinEquiv L_m L_k r r'.
    ∅-axiom. -/
theorem gcd_subset_joinEquiv (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (r r' : Raw) (h : (leavesModNat (gcd213 m k)).equiv r r') :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  by_cases hmk : m ≥ k
  · exact join_eq_gcd_JE_sorted (m + k) m k (Nat.le_refl _) hmk hm hk r r' h
  · have hkm : k ≥ m := Nat.le_of_lt (Nat.lt_of_not_le hmk)
    have h_swap : (leavesModNat (gcd213 k m)).equiv r r' := by
      show (leavesModNat (gcd213 k m)).view r = (leavesModNat (gcd213 k m)).view r'
      rw [gcd213_comm]
      exact h
    have := join_eq_gcd_JE_sorted (k + m) k m (Nat.le_refl _) hkm hk hm r r' h_swap
    exact swap_JE k m r r' this

/-- **Equivalence**: L_{gcd213}.equiv = JoinEquiv L_m L_k on Raw × Raw.
    ∅-axiom. -/
theorem gcd_equiv_joinEquiv (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (r r' : Raw) :
    (leavesModNat (gcd213 m k)).equiv r r' ↔
      JoinEquiv (leavesModNat m) (leavesModNat k) r r' :=
  ⟨gcd_subset_joinEquiv m k hm hk r r',
   E213.Lib.Math.ModArith.JoinGCD.joinEquiv_subset_gcd m k r r'⟩

end E213.Lib.Math.ModArith.JoinEquivGCD
