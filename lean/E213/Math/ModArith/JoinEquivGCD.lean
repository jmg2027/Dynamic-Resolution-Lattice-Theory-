import E213.Math.ModArith.JoinGCD

/-!
# ModJoinEquivGCD: L_gcd.equiv ⊆ JoinEquiv L_m L_k

The **converse direction** of `ModJoinGCD.joinEquiv_subset_gcd`.
Together they establish **L_gcd.equiv = JoinEquiv L_m L_k** —
that is, **L_gcd is the concrete Lens realization of JoinEquiv**
(for the mod family).

This resolves the "concrete Quot Lens construction" open problem of
note 48 for the mod family.

## Strategy

Reconstructs the chain proof structure of
`ModJoinGCD.join_refines_gcd` at the JoinEquiv level.  Each claim
`N.view r = N.view r'` is replaced with `JoinEquiv L_m L_k r r'`,
and the refinement application of `hLm`, `hLk` is replaced with the
`ofL`, `ofM` constructors.
-/

namespace E213.Math.ModArith.JoinEquivGCD

open E213.Theory E213.Lens
open E213.Lens.Leaves.ModNat E213.Lens.Lattice.JoinEquiv E213.Math.ModArith.JoinGCD

private theorem leaves_ge_one_local (r : Raw) : 1 ≤ Lens.leaves.view r := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]; omega

/-- **Chain step** at the JE level: when m > k ≥ 2,
    `leaves r' = leaves r + (m - k) → JoinEquiv L_m L_k r r'`.
    Reconstruction of `ModJoinBezout.chain_step_sub` at the JE level. -/
theorem chain_step_sub_JE (m k : Nat) (hk : k ≥ 2) (hmk : m > k)
    (r r' : Raw) (hdiff : Lens.leaves.view r' = Lens.leaves.view r + (m - k)) :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  obtain ⟨w, hw⟩ := E213.Infinity.leaves_surjective_pos
    (Lens.leaves.view r + m) (by omega)
  have h_rw_m : (leavesModNat m).equiv r w := by
    show (leavesModNat m).view r = (leavesModNat m).view w
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, Nat.add_mod_right]
  have h_wr'_k : (leavesModNat k).equiv w r' := by
    show (leavesModNat k).view w = (leavesModNat k).view r'
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hw, hdiff]
    have : Lens.leaves.view r + m
             = (Lens.leaves.view r + (m - k)) + k := by omega
    rw [this, Nat.add_mod_right]
  exact JoinEquiv.trans (JoinEquiv.ofL h_rw_m) (JoinEquiv.ofM h_wr'_k)

/-- **Same leaves** → JoinEquiv via ofL (L_m.equiv x y). -/
theorem same_leaves_JE (m k : Nat)
    (r r' : Raw) (hr : Lens.leaves.view r = Lens.leaves.view r') :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  apply JoinEquiv.ofL
  show (leavesModNat m).view r = (leavesModNat m).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, hr]

/-- **+n(m-k) chain** at the JE level.  Reconstruction of
    `ModJoinEuclidean.step_plus_nd` at the JE level. -/
theorem step_plus_nd_JE (m k : Nat) (hk : k ≥ 2) (hmk : m > k)
    (r : Raw) (n : Nat) :
    ∀ r', Lens.leaves.view r' = Lens.leaves.view r + n * (m - k) →
        JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  induction n with
  | zero =>
      intro r' hr'
      apply same_leaves_JE m k
      omega
  | succ n ih =>
      intro r' hr'
      have h_r_ge : 1 ≤ Lens.leaves.view r := leaves_ge_one_local r
      have h_bound : 1 ≤ Lens.leaves.view r + n * (m - k) := by
        have : 0 ≤ n * (m - k) := Nat.zero_le _
        omega
      obtain ⟨r'', hr''⟩ :=
        E213.Infinity.leaves_surjective_pos
          (Lens.leaves.view r + n * (m - k)) h_bound
      have step1 : JoinEquiv (leavesModNat m) (leavesModNat k) r r'' :=
        ih r'' hr''
      have hexpand : (n + 1) * (m - k) = n * (m - k) + (m - k) :=
        Nat.succ_mul n (m - k)
      have step2 : JoinEquiv (leavesModNat m) (leavesModNat k) r'' r' := by
        apply chain_step_sub_JE m k hk hmk r'' r'
        rw [hr', hr'', hexpand]
        omega
      exact JoinEquiv.trans step1 step2

/-- **Euclidean step** at JE level.  L_{m-k}.equiv r r' →
    JoinEquiv L_m L_k r r'. -/
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
  have hd_pos : m - k > 0 := by omega
  have key : ∀ (a b : Nat), a % (m - k) = b % (m - k) → b ≤ a →
             a = b + ((a - b) / (m - k)) * (m - k) := by
    intro a b hmod hab
    have hb_le_a_div : b / (m - k) ≤ a / (m - k) := by
      by_cases hle : b / (m - k) ≤ a / (m - k)
      · exact hle
      · exfalso
        have hlt : a / (m - k) < b / (m - k) := Nat.lt_of_not_le hle
        have hgt : b / (m - k) ≥ a / (m - k) + 1 := hlt
        have hmul_ge : (m - k) * (a / (m - k) + 1) ≤ (m - k) * (b / (m - k)) :=
          Nat.mul_le_mul_left _ hgt
        have hexp : (m - k) * (a / (m - k) + 1)
                      = (m - k) * (a / (m - k)) + (m - k) :=
          Nat.mul_succ (m - k) (a / (m - k))
        have h1 := Nat.div_add_mod a (m - k)
        have h2 := Nat.div_add_mod b (m - k)
        have hamod := Nat.mod_lt a hd_pos
        omega
    have hsub : a - b = (m - k) * (a / (m - k) - b / (m - k)) := by
      rw [Nat.mul_sub_left_distrib]
      have h1 := Nat.div_add_mod a (m - k)
      have h2 := Nat.div_add_mod b (m - k)
      omega
    rw [hsub, Nat.mul_div_cancel_left _ hd_pos, Nat.mul_comm]
    omega
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · exact step_plus_nd_JE m k hk hmk r _ r' (key _ _ h_mod.symm hle)
  · exact JoinEquiv.symm
      (step_plus_nd_JE m k hk hmk r' _ r (key _ _ h_mod hle))

/-- **Consecutive** at the JE level.  When m = k + 1, JoinEquiv L_m L_k
    holds for all r, r' (since L_1.equiv is always true). -/
theorem consecutive_refines_all_JE (m k : Nat) (hk : k ≥ 2) (hms : m = k + 1) :
    ∀ r r' : Raw, JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  intro r r'
  have hmk : m > k := by omega
  have hdiff : m - k = 1 := by omega
  rcases Nat.le_total (Lens.leaves.view r) (Lens.leaves.view r') with hle | hle
  · apply step_plus_nd_JE m k hk hmk r (Lens.leaves.view r' - Lens.leaves.view r) r'
    rw [hdiff, Nat.mul_one]
    omega
  · exact JoinEquiv.symm
      (step_plus_nd_JE m k hk hmk r' (Lens.leaves.view r - Lens.leaves.view r') r
        (by rw [hdiff, Nat.mul_one]; omega))

/-- **Lifting**: JoinEquiv L_{m-k} L_k → JoinEquiv L_m L_k.
    Induct on JoinEquiv.  ofL uses euclidean_step_JE, ofM lifts
    directly, and the remaining equivalence/congruence constructors
    lift isomorphically. -/
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

/-- **Swap** (symmetric in L, M): JoinEquiv L_m L_k ↔ JoinEquiv L_k L_m. -/
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

/-- **Main theorem at the JE level (sorted)**: strong induction on
    m + k, assuming m ≥ k.
    L_gcd.equiv r r' → JoinEquiv L_m L_k r r'. -/
private theorem join_eq_gcd_JE_sorted :
    ∀ (s m k : Nat), m + k ≤ s → m ≥ k → m ≥ 2 → k ≥ 2 →
    ∀ r r' : Raw, (leavesModNat (Nat.gcd m k)).equiv r r' →
      JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  intro s
  induction s with
  | zero =>
      intro m k _ _ hm _ _ _ _
      omega
  | succ n ih =>
      intro m k hsum _ hm hk r r' hrr'
      by_cases heq : m = k
      · apply JoinEquiv.ofL
        rw [heq] at hrr'
        have : Nat.gcd k k = k := Nat.gcd_self k
        rw [this] at hrr'
        rw [heq]
        exact hrr'
      · have hmgt : m > k := by omega
        by_cases hd1 : m - k = 1
        · have hms : m = k + 1 := by omega
          exact consecutive_refines_all_JE m k hk hms r r'
        · have hd2 : m - k ≥ 2 := by omega
          have hrec_hyp : (leavesModNat (Nat.gcd (m - k) k)).equiv r r' := by
            have hgcd_eq : Nat.gcd (m - k) k = Nat.gcd m k := by
              have hexp : (m - k) + k = m := by omega
              calc Nat.gcd (m - k) k
                  = Nat.gcd k (m - k) := Nat.gcd_comm _ _
                _ = Nat.gcd (((m - k) + k) % k) k := by
                    rw [Nat.gcd_rec, Nat.add_mod_right]
                _ = Nat.gcd (m % k) k := by rw [hexp]
                _ = Nat.gcd k m := (Nat.gcd_rec _ _).symm
                _ = Nat.gcd m k := Nat.gcd_comm _ _
            show (leavesModNat (Nat.gcd (m - k) k)).view r
                 = (leavesModNat (Nat.gcd (m - k) k)).view r'
            rw [hgcd_eq]
            exact hrr'
          by_cases hmkge : m - k ≥ k
          · have hrec : JoinEquiv (leavesModNat (m - k)) (leavesModNat k) r r' :=
              ih (m - k) k (by omega) hmkge hd2 hk r r' hrec_hyp
            exact lift_sub_JE m k hk hmgt hd2 r r' hrec
          · have hklt : k > m - k := Nat.lt_of_not_le hmkge
            have hrec_swap : (leavesModNat (Nat.gcd k (m - k))).equiv r r' := by
              show (leavesModNat (Nat.gcd k (m - k))).view r
                   = (leavesModNat (Nat.gcd k (m - k))).view r'
              rw [Nat.gcd_comm]
              exact hrec_hyp
            have hrec : JoinEquiv (leavesModNat k) (leavesModNat (m - k)) r r' :=
              ih k (m - k) (by omega) (by omega) hk hd2 r r' hrec_swap
            have hrec' : JoinEquiv (leavesModNat (m - k)) (leavesModNat k) r r' :=
              swap_JE k (m - k) r r' hrec
            exact lift_sub_JE m k hk hmgt hd2 r r' hrec'

/-- **Main theorem at the JE level**: L_gcd.equiv r r' → JoinEquiv L_m L_k r r'.
    Converse direction of `ModJoinGCD.joinEquiv_subset_gcd`. -/
theorem gcd_subset_joinEquiv (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (r r' : Raw) (h : (leavesModNat (Nat.gcd m k)).equiv r r') :
    JoinEquiv (leavesModNat m) (leavesModNat k) r r' := by
  by_cases hmk : m ≥ k
  · exact join_eq_gcd_JE_sorted (m + k) m k (Nat.le_refl _) hmk hm hk r r' h
  · have hkm : k ≥ m := Nat.le_of_lt (Nat.lt_of_not_le hmk)
    have h_swap : (leavesModNat (Nat.gcd k m)).equiv r r' := by
      show (leavesModNat (Nat.gcd k m)).view r = (leavesModNat (Nat.gcd k m)).view r'
      rw [Nat.gcd_comm]
      exact h
    have := join_eq_gcd_JE_sorted (k + m) k m (Nat.le_refl _) hkm hk hm r r' h_swap
    exact swap_JE k m r r' this

/-- **Equivalence**: L_gcd.equiv = JoinEquiv L_m L_k on Raw × Raw.
    Concrete Quot Lens construction for the mod family case. -/
theorem gcd_equiv_joinEquiv (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (r r' : Raw) :
    (leavesModNat (Nat.gcd m k)).equiv r r' ↔
      JoinEquiv (leavesModNat m) (leavesModNat k) r r' :=
  ⟨gcd_subset_joinEquiv m k hm hk r r',
   E213.Math.ModArith.JoinGCD.joinEquiv_subset_gcd m k r r'⟩

end E213.Math.ModArith.JoinEquivGCD
