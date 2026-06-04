import E213.Lib.Math.Cohomology.Bipartite.V33EnrichedParametricDualSpanHard

/-!
# Per-layer completeness: ∀c lift via layer-disjointness

★★★★★★★★★★★★★★★ **HARD direction at arbitrary c via layer
promotion.** ★★★★★★★★★★★★★★★

Companion to `V33EnrichedParametricDualSpanHard` (which closes the
c=1 HARD direction).  This file lifts the result to every `c ≥ 1`
via the layer-promotion map:

  `promote : EnrichedFaceVal 1 → (Fin c → EnrichedFaceVal c)`

For `w ∈ InPrimary 1`, `promote c m w` is supported only at layer m
of `EnrichedFaceVal c`, mirroring `w` at layer 0 elsewhere.  The
key lemma `promote_in_primary` shows InPrimary is preserved under
this promotion, by induction on the inductive structure of
`InPrimary 1`.

## Strategy

1. **Promote** edge cochains (`promote_edge`) and face cochains
   (`promote_face`) from level 1 to level c at any chosen layer.
2. **Promote-coboundary**: `promote(δ¹(σ))` pointwise equals
   `δ¹(promote_edge σ)` (verified via edge-index arithmetic).
3. **Promote-starCup**: `promote(cupOpp(starS 0, β))` pointwise
   equals `cupOpp(starS c i m, promote_edge β)` (verified via
   `starS_at_edge_idx_same_m` and cross-layer vanishing).
4. **Promote-incidCup**: symmetric.
5. **Promote-xor**: distributes pointwise.
6. **Capstone**: for any `v` with `∀m, ψ_m(v) = 0`, decompose
   `v = ⊕_m promote c m (layer_slice c m v)` pointwise; each
   summand is in InPrimary by the lift + c=1 theorem; closure
   under `xor_add` and `cong` finishes.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V33EnrichedParametricDualSpanHardLift

open E213.Lib.Math.Cohomology.Bipartite.V33EnrichedParametric
open E213.Lib.Math.Cohomology.Bipartite.V33EnrichedParametricDualSpan
open E213.Lib.Math.Cohomology.Bipartite.V33EnrichedParametricDualSpanHard
open E213.Meta.Nat.Beq213

/-! ## §1 — Layer slice and promotion -/

/-- Layer-m slice of a `c`-level face cochain, viewed as a c=1 face
    cochain.  Reads only the m-th layer of v. -/
def layer_slice (c : Nat) (m : Fin c) (v : EnrichedFaceVal c) : EnrichedFaceVal 1 :=
  fun s t _ => v s t m

/-- Promote a c=1 face cochain to layer m of `EnrichedFaceVal c`.
    Returns `w s t m0` at layer m, zero elsewhere. -/
def promote_face (c : Nat) (m : Fin c) (w : EnrichedFaceVal 1) : EnrichedFaceVal c :=
  fun s t m' => decide (m'.val = m.val) && w s t m0

/-- Promote a c=1 edge cochain to layer m of `EnrichedEdgeCoch c`.
    Inlined as a nested `cond` cascade over offsets `0..8` (avoiding
    `Nat.div`/`Nat.mod` which pull `propext` via `Nat.div_eq_of_lt`,
    and avoiding trailing `|| false` which doesn't reduce by `rfl`
    for abstract Bool tails). -/
def promote_edge (c : Nat) (m : Fin c) (σ : EnrichedEdgeCoch 1) : EnrichedEdgeCoch c :=
  fun e =>
    cond (e.val == 9 * m.val + 0) (σ ⟨0, by decide⟩) (
    cond (e.val == 9 * m.val + 1) (σ ⟨1, by decide⟩) (
    cond (e.val == 9 * m.val + 2) (σ ⟨2, by decide⟩) (
    cond (e.val == 9 * m.val + 3) (σ ⟨3, by decide⟩) (
    cond (e.val == 9 * m.val + 4) (σ ⟨4, by decide⟩) (
    cond (e.val == 9 * m.val + 5) (σ ⟨5, by decide⟩) (
    cond (e.val == 9 * m.val + 6) (σ ⟨6, by decide⟩) (
    cond (e.val == 9 * m.val + 7) (σ ⟨7, by decide⟩) (
    cond (e.val == 9 * m.val + 8) (σ ⟨8, by decide⟩) false))))))))

/-! ## §2 — Basic correctness of the promotion

The ψ-functional respects layer slicing; this lets the c=1 theorem
apply to each slice. -/

theorem psi_layer_of_layer_slice (c : Nat) (m : Fin c) (v : EnrichedFaceVal c) :
    psi_layer 1 m0 (layer_slice c m v) = psi_layer c m v := rfl

/-- `(edge_idx 1 p q m0).val = 3p + q` (the c=1, layer-0 edge index). -/
private theorem edge_idx_one_val (p q : Fin 3) :
    (edge_idx 1 p q m0).val = 3 * p.val + q.val := by
  show 9 * 0 + 3 * p.val + q.val = 3 * p.val + q.val
  rw [Nat.mul_zero, Nat.add_assoc, Nat.zero_add]

/-- Convert `σ ⟨3p+q, _⟩` to `σ (edge_idx 1 p q m0)` via Fin.ext. -/
private theorem sigma_at_offset_eq (σ : EnrichedEdgeCoch 1) (p q : Fin 3)
    (k : Nat) (hk : k < 9) (h_eq : k = 3 * p.val + q.val) :
    σ ⟨k, hk⟩ = σ (edge_idx 1 p q m0) := by
  congr 1
  apply Fin.ext
  show k = (edge_idx 1 p q m0).val
  rw [edge_idx_one_val, h_eq]

/-- `promote_edge` evaluated at the layer-m edge `(p, q, m)` returns
    the c=1 value at edge `(p, q, ⟨0,_⟩)`.  After cancelling the
    `9·m` prefix via `nat_decide_add_left_assoc1`, each (p, q) case
    reduces by `rfl` because the cond cascade resolves to the unique
    matching offset. -/
theorem promote_edge_at_layer_m (c : Nat) (m : Fin c) (σ : EnrichedEdgeCoch 1)
    (p q : Fin 3) :
    promote_edge c m σ (edge_idx c p q m) = σ (edge_idx 1 p q m0) := by
  unfold promote_edge
  show (cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 0) (σ ⟨0, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 1) (σ ⟨1, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 2) (σ ⟨2, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 3) (σ ⟨3, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 4) (σ ⟨4, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 5) (σ ⟨5, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 6) (σ ⟨6, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 7) (σ ⟨7, _⟩) (
        cond (9 * m.val + 3 * p.val + q.val == 9 * m.val + 8) (σ ⟨8, _⟩) false)))))))))
       = σ (edge_idx 1 p q m0)
  rw [nat_decide_add_left_assoc1, nat_decide_add_left_assoc1, nat_decide_add_left_assoc1,
      nat_decide_add_left_assoc1, nat_decide_add_left_assoc1, nat_decide_add_left_assoc1,
      nat_decide_add_left_assoc1, nat_decide_add_left_assoc1, nat_decide_add_left_assoc1]
  match p, q with
  | ⟨0, _⟩, ⟨0, _⟩ => show σ ⟨0, by decide⟩ = σ (edge_idx 1 ⟨0, by decide⟩ ⟨0, by decide⟩ m0); rfl
  | ⟨0, _⟩, ⟨1, _⟩ => show σ ⟨1, by decide⟩ = σ (edge_idx 1 ⟨0, by decide⟩ ⟨1, by decide⟩ m0); rfl
  | ⟨0, _⟩, ⟨2, _⟩ => show σ ⟨2, by decide⟩ = σ (edge_idx 1 ⟨0, by decide⟩ ⟨2, by decide⟩ m0); rfl
  | ⟨1, _⟩, ⟨0, _⟩ => show σ ⟨3, by decide⟩ = σ (edge_idx 1 ⟨1, by decide⟩ ⟨0, by decide⟩ m0); rfl
  | ⟨1, _⟩, ⟨1, _⟩ => show σ ⟨4, by decide⟩ = σ (edge_idx 1 ⟨1, by decide⟩ ⟨1, by decide⟩ m0); rfl
  | ⟨1, _⟩, ⟨2, _⟩ => show σ ⟨5, by decide⟩ = σ (edge_idx 1 ⟨1, by decide⟩ ⟨2, by decide⟩ m0); rfl
  | ⟨2, _⟩, ⟨0, _⟩ => show σ ⟨6, by decide⟩ = σ (edge_idx 1 ⟨2, by decide⟩ ⟨0, by decide⟩ m0); rfl
  | ⟨2, _⟩, ⟨1, _⟩ => show σ ⟨7, by decide⟩ = σ (edge_idx 1 ⟨2, by decide⟩ ⟨1, by decide⟩ m0); rfl
  | ⟨2, _⟩, ⟨2, _⟩ => show σ ⟨8, by decide⟩ = σ (edge_idx 1 ⟨2, by decide⟩ ⟨2, by decide⟩ m0); rfl
  | ⟨n+3, h⟩, _ => exfalso; exact absurd (Nat.le_add_left 3 n) (Nat.not_le_of_lt h)
  | _, ⟨n+3, h⟩ => exfalso; exact absurd (Nat.le_add_left 3 n) (Nat.not_le_of_lt h)

/-- Helper: the 9-fold nested `cond` is `false` when all guards are `false`. -/
private theorem nine_cond_all_false_eq_false
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 : Bool) :
    cond false s0 (cond false s1 (cond false s2 (cond false s3
      (cond false s4 (cond false s5 (cond false s6 (cond false s7
        (cond false s8 false))))))) ) = false := rfl

/-- `promote_edge` evaluated at a non-layer-m edge `(p, q, m')` with
    `m' ≠ m` returns `false`.  All 9 cond guards are false (by
    `nine_block_disjoint_op`), reducing the cascade to `false`. -/
theorem promote_edge_at_layer_other (c : Nat) (m m' : Fin c) (h_ne : m.val ≠ m'.val)
    (σ : EnrichedEdgeCoch 1) (p q : Fin 3) :
    promote_edge c m σ (edge_idx c p q m') = false := by
  have hp : p.val ≤ 2 := Nat.le_of_lt_succ p.isLt
  have hq : q.val ≤ 2 := Nat.le_of_lt_succ q.isLt
  have h3pq_lt : 3 * p.val + q.val < 9 := by
    have h3p : 3 * p.val ≤ 6 := Nat.mul_le_mul_left 3 hp
    exact Nat.lt_of_le_of_lt (Nat.add_le_add h3p hq) (by decide)
  have h_mne : m'.val ≠ m.val := Ne.symm h_ne
  show cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 0) (σ ⟨0, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 1) (σ ⟨1, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 2) (σ ⟨2, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 3) (σ ⟨3, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 4) (σ ⟨4, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 5) (σ ⟨5, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 6) (σ ⟨6, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 7) (σ ⟨7, _⟩) (
       cond (9 * m'.val + 3 * p.val + q.val == 9 * m.val + 8) (σ ⟨8, _⟩) false)))))))) = false
  rw [show 9 * m'.val + 3 * p.val + q.val = 9 * m'.val + (3 * p.val + q.val)
        from Nat.add_assoc _ _ _,
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 0 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 1 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 2 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 3 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 4 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 5 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 6 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 7 < 9),
      nine_block_disjoint_op h_mne h3pq_lt (by decide : 8 < 9)]
  exact nine_cond_all_false_eq_false _ _ _ _ _ _ _ _ _

/-! ## §3 — `starS` and `incidT` evaluation at same layer

Both `starS c i m` and `incidT c j m` evaluate at `edge_idx c p q m`
to expressions independent of `m`, matching the c=1, layer-0 case.
This is the basis for cup-product transport across c and m. -/

theorem starS_at_layer_match (c : Nat) (i : Fin 3) (m : Fin c) (p q : Fin 3) :
    starS c i m (edge_idx c p q m) = starS 1 i m0 (edge_idx 1 p q m0) := by
  rw [starS_at_edge_idx_same_m c i p q m, starS_at_edge_idx_same_m 1 i p q m0]

theorem incidT_at_layer_match (c : Nat) (j : Fin 3) (m : Fin c) (p q : Fin 3) :
    incidT c j m (edge_idx c p q m) = incidT 1 j m0 (edge_idx 1 p q m0) := by
  rw [incidT_at_edge_idx_same_m c j p q m, incidT_at_edge_idx_same_m 1 j p q m0]

/-! ## §4 — Pointwise equalities for the 5 constructors

For each constructor of `InPrimary 1`, the promoted face cochain
matches a corresponding `InPrimary c` construction pointwise. -/

/-- Zero is preserved by promotion (and is trivially zero everywhere). -/
theorem promote_zero (c : Nat) (m : Fin c) (s t : Fin 3) (m' : Fin c) :
    promote_face c m (fun _ _ _ => false) s t m'
      = (fun (_ _ : Fin 3) (_ : Fin c) => false) s t m' := by
  unfold promote_face
  cases decide (m'.val = m.val) <;> rfl

/-- Helper: at a same-layer edge `(p, q, m)`, both the cup's first
    factor (starS / α) and second factor (promote_edge / β) match
    their c=1, layer-0 counterparts. -/
private theorem cup_factors_at_layer_m_eq (c : Nat) (m : Fin c)
    (α₁ : EnrichedEdgeCoch 1) (αc : EnrichedEdgeCoch c)
    (β₁ : EnrichedEdgeCoch 1) (βc : EnrichedEdgeCoch c)
    (hα : ∀ p q : Fin 3, αc (edge_idx c p q m) = α₁ (edge_idx 1 p q m0))
    (hβ : ∀ p q : Fin 3, βc (edge_idx c p q m) = β₁ (edge_idx 1 p q m0))
    (s t : Fin 3) :
    cupOpp_param c αc βc s t m = cupOpp_param 1 α₁ β₁ s t m0 := by
  unfold cupOpp_param diag_pair_param
  rw [hα (pair_lo s) (pair_lo t), hα (pair_hi s) (pair_hi t),
      hα (pair_hi s) (pair_lo t), hα (pair_lo s) (pair_hi t),
      hβ (pair_lo s) (pair_lo t), hβ (pair_hi s) (pair_hi t),
      hβ (pair_hi s) (pair_lo t), hβ (pair_lo s) (pair_hi t)]

/-- Coboundary is preserved: promotion of `δ¹(σ)` equals `δ¹(promote_edge σ)`. -/
theorem promote_coboundary (c : Nat) (m : Fin c) (σ : EnrichedEdgeCoch 1)
    (s t : Fin 3) (m' : Fin c) :
    promote_face c m (delta1_enr_param 1 σ) s t m'
      = delta1_enr_param c (promote_edge c m σ) s t m' := by
  unfold promote_face delta1_enr_param face_boundary_stm
  cases hmm : decide (m'.val = m.val) with
  | true =>
      have hm : m' = m := Fin.ext (of_decide_eq_true hmm)
      rw [hm]
      show (true && _) = _
      rw [Bool.true_and,
          promote_edge_at_layer_m c m σ (pair_lo s) (pair_lo t),
          promote_edge_at_layer_m c m σ (pair_lo s) (pair_hi t),
          promote_edge_at_layer_m c m σ (pair_hi s) (pair_lo t),
          promote_edge_at_layer_m c m σ (pair_hi s) (pair_hi t)]
  | false =>
      have hm_ne : m'.val ≠ m.val := of_decide_eq_false hmm
      show (false && _) = _
      rw [Bool.false_and,
          promote_edge_at_layer_other c m m' (Ne.symm hm_ne) σ (pair_lo s) (pair_lo t),
          promote_edge_at_layer_other c m m' (Ne.symm hm_ne) σ (pair_lo s) (pair_hi t),
          promote_edge_at_layer_other c m m' (Ne.symm hm_ne) σ (pair_hi s) (pair_lo t),
          promote_edge_at_layer_other c m m' (Ne.symm hm_ne) σ (pair_hi s) (pair_hi t)]
      rfl

/-- starCup is preserved: promotion of `cup(starS 1 i 0, β)` equals
    `cup(starS c i m, promote_edge β)`. -/
theorem promote_starCup (c : Nat) (m : Fin c) (i : Fin 3)
    (β : EnrichedEdgeCoch 1) (s t : Fin 3) (m' : Fin c) :
    promote_face c m (cupOpp_param 1 (starS 1 i m0) β) s t m'
      = cupOpp_param c (starS c i m) (promote_edge c m β) s t m' := by
  unfold promote_face
  cases hmm : decide (m'.val = m.val) with
  | true =>
      have hm : m' = m := Fin.ext (of_decide_eq_true hmm)
      rw [hm]
      show (true && _) = _
      rw [Bool.true_and]
      exact (cup_factors_at_layer_m_eq c m (starS 1 i m0) (starS c i m) β
        (promote_edge c m β) (starS_at_layer_match c i m)
        (promote_edge_at_layer_m c m β) s t).symm
  | false =>
      have hm_ne : m'.val ≠ m.val := of_decide_eq_false hmm
      show (false && _) = _
      rw [Bool.false_and]
      exact (cupOpp_starS_cross_layer_zero c i m m'
        (Ne.symm hm_ne) (promote_edge c m β) s t).symm

/-- incidCup is preserved: promotion of `cup(α, incidT 1 j 0)` equals
    `cup(promote_edge α, incidT c j m)`. -/
theorem promote_incidCup (c : Nat) (m : Fin c) (j : Fin 3)
    (α : EnrichedEdgeCoch 1) (s t : Fin 3) (m' : Fin c) :
    promote_face c m (cupOpp_param 1 α (incidT 1 j m0)) s t m'
      = cupOpp_param c (promote_edge c m α) (incidT c j m) s t m' := by
  unfold promote_face
  cases hmm : decide (m'.val = m.val) with
  | true =>
      have hm : m' = m := Fin.ext (of_decide_eq_true hmm)
      rw [hm]
      show (true && _) = _
      rw [Bool.true_and]
      exact (cup_factors_at_layer_m_eq c m α (promote_edge c m α) (incidT 1 j m0) (incidT c j m)
        (promote_edge_at_layer_m c m α) (incidT_at_layer_match c j m) s t).symm
  | false =>
      have hm_ne : m'.val ≠ m.val := of_decide_eq_false hmm
      show (false && _) = _
      rw [Bool.false_and]
      exact (cupOpp_incidT_cross_layer_zero c j m m'
        (Ne.symm hm_ne) (promote_edge c m α) s t).symm

/-- XOR-add is preserved: promotion distributes over pointwise XOR. -/
theorem promote_xor_add (c : Nat) (m : Fin c) (v w : EnrichedFaceVal 1)
    (s t : Fin 3) (m' : Fin c) :
    promote_face c m (fun s' t' m'' => xor (v s' t' m'') (w s' t' m'')) s t m'
      = xor (promote_face c m v s t m') (promote_face c m w s t m') := by
  unfold promote_face
  cases decide (m'.val = m.val) <;> rfl

/-- Forced `m' = m0` for `m' : Fin 1`. -/
private theorem fin1_unique (m' : Fin 1) : m' = m0 := by
  match m' with
  | ⟨0, _⟩ => rfl
  | ⟨n+1, h⟩ => exfalso; exact absurd (Nat.le_add_left 1 n) (Nat.not_le_of_lt h)

/-! ## §5 — Main lift: `InPrimary 1 w → InPrimary c (promote_face c m w)`

By induction on the 6 constructors of `InPrimaryCupSpanPlusBoundary 1`. -/

theorem promote_in_primary (c : Nat) (m : Fin c) (w : EnrichedFaceVal 1)
    (hw : InPrimaryCupSpanPlusBoundary 1 w) :
    InPrimaryCupSpanPlusBoundary c (promote_face c m w) := by
  induction hw with
  | zero =>
      apply InPrimaryCupSpanPlusBoundary.cong (promote_face c m (fun _ _ _ => false))
        (fun _ _ _ => false) (promote_zero c m)
      exact InPrimaryCupSpanPlusBoundary.zero
  | coboundary σ =>
      apply InPrimaryCupSpanPlusBoundary.cong (promote_face c m (delta1_enr_param 1 σ))
        (delta1_enr_param c (promote_edge c m σ)) (promote_coboundary c m σ)
      exact InPrimaryCupSpanPlusBoundary.coboundary (promote_edge c m σ)
  | starCup i mm β =>
      rw [fin1_unique mm]
      apply InPrimaryCupSpanPlusBoundary.cong
        (promote_face c m (cupOpp_param 1 (starS 1 i m0) β))
        (cupOpp_param c (starS c i m) (promote_edge c m β))
        (promote_starCup c m i β)
      exact InPrimaryCupSpanPlusBoundary.starCup i m (promote_edge c m β)
  | incidCup j mm α =>
      rw [fin1_unique mm]
      apply InPrimaryCupSpanPlusBoundary.cong
        (promote_face c m (cupOpp_param 1 α (incidT 1 j m0)))
        (cupOpp_param c (promote_edge c m α) (incidT c j m))
        (promote_incidCup c m j α)
      exact InPrimaryCupSpanPlusBoundary.incidCup j m (promote_edge c m α)
  | xor_add v w _ _ ihv ihw =>
      apply InPrimaryCupSpanPlusBoundary.cong
        (promote_face c m (fun s' t' m'' => xor (v s' t' m'') (w s' t' m'')))
        (fun s t m' => xor (promote_face c m v s t m') (promote_face c m w s t m'))
        (promote_xor_add c m v w)
      exact InPrimaryCupSpanPlusBoundary.xor_add _ _ ihv ihw
  | cong v w h_eq _ ih =>
      apply InPrimaryCupSpanPlusBoundary.cong (promote_face c m v) (promote_face c m w)
        (fun s t mm => by unfold promote_face; rw [h_eq s t m0])
      exact ih

/-! ## §6 — Iterated XOR aggregator over the first `k` layers

`xor_aggregate c v k hk` is the XOR-sum (as a face cochain) of
`promote_face c ⟨k', _⟩ (layer_slice c ⟨k', _⟩ v)` for `k' ∈ [0, k)`.

When `k = c`, this aggregates over all layers and the result equals
`v` pointwise (assuming `∀ m, ψ_m(v) = false`, so each layer slice
lies in InPrimary 1). -/

def xor_aggregate (c : Nat) (v : EnrichedFaceVal c) :
    (k : Nat) → k ≤ c → EnrichedFaceVal c
  | 0, _ => fun _ _ _ => false
  | k+1, hk =>
      let k_fin : Fin c := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      fun s t m' =>
        xor (promote_face c k_fin (layer_slice c k_fin v) s t m')
            (xor_aggregate c v k (Nat.le_of_succ_le hk) s t m')

/-- Each `xor_aggregate` lies in `InPrimary c`, given that each layer
    slice is in `InPrimary 1` (i.e., satisfies `ψ_m(v) = 0`). -/
theorem xor_aggregate_in_primary (c : Nat) (v : EnrichedFaceVal c)
    (hv : ∀ m, psi_layer c m v = false) :
    ∀ (k : Nat) (hk : k ≤ c),
      InPrimaryCupSpanPlusBoundary c (xor_aggregate c v k hk) := by
  intro k
  induction k with
  | zero =>
      intro _; exact InPrimaryCupSpanPlusBoundary.zero
  | succ k ih =>
      intro hk
      unfold xor_aggregate
      apply InPrimaryCupSpanPlusBoundary.xor_add
      · let k_fin : Fin c := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
        apply promote_in_primary c k_fin
        exact joint_psi_kernel_subset_primary_c1 (layer_slice c k_fin v)
          (by show psi_layer 1 m0 (layer_slice c k_fin v) = false; exact hv k_fin)
      · exact ih (Nat.le_of_succ_le hk)

/-- Pointwise invariant: at position `(s, t, m')`, the aggregate over
    the first `k` layers equals `v s t m'` if `m'.val < k`, else `false`. -/
theorem xor_aggregate_val (c : Nat) (v : EnrichedFaceVal c)
    (s t : Fin 3) (m' : Fin c) :
    ∀ (k : Nat) (hk : k ≤ c),
      xor_aggregate c v k hk s t m'
        = (decide (m'.val < k) && v s t m') := by
  intro k
  induction k with
  | zero =>
      intro _
      show false = (decide (m'.val < 0) && v s t m')
      rw [show decide (m'.val < 0) = false from decide_eq_false (Nat.not_lt_zero _)]
      rfl
  | succ k ih =>
      intro hk
      unfold xor_aggregate
      let k_fin : Fin c := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      show xor (promote_face c k_fin (layer_slice c k_fin v) s t m')
                (xor_aggregate c v k _ s t m')
            = (decide (m'.val < k+1) && v s t m')
      rw [ih (Nat.le_of_succ_le hk)]
      show xor (decide (m'.val = k_fin.val) && layer_slice c k_fin v s t m0)
                (decide (m'.val < k) && v s t m')
            = (decide (m'.val < k+1) && v s t m')
      cases hlt : decide (m'.val < k) with
      | true =>
          have hlt' : m'.val < k := of_decide_eq_true hlt
          have hne : m'.val ≠ k_fin.val := Nat.ne_of_lt hlt'
          have hlt_succ : m'.val < k + 1 := Nat.lt_succ_of_lt hlt'
          rw [decide_eq_false hne, decide_eq_true hlt_succ, Bool.false_and, Bool.true_and]
          cases v s t m' <;> rfl
      | false =>
          have hge : ¬ m'.val < k := of_decide_eq_false hlt
          have hge' : k ≤ m'.val := Nat.le_of_not_lt hge
          rw [Bool.false_and]
          show xor (decide (m'.val = k_fin.val) && layer_slice c k_fin v s t m0) false
                = (decide (m'.val < k+1) && v s t m')
          cases heq : decide (m'.val = k_fin.val) with
          | true =>
              have heq' : m'.val = k_fin.val := of_decide_eq_true heq
              have heq'' : m'.val = k := heq'
              have hlt_succ : m'.val < k + 1 := by rw [heq'']; exact Nat.lt_succ_self _
              rw [decide_eq_true hlt_succ, Bool.true_and]
              show xor (layer_slice c k_fin v s t m0) false = v s t m'
              unfold layer_slice
              show xor (v s t k_fin) false = v s t m'
              have h_eq : v s t k_fin = v s t m' := by congr 1; exact Fin.ext heq''.symm
              rw [h_eq]; cases v s t m' <;> rfl
          | false =>
              have hne : m'.val ≠ k_fin.val := of_decide_eq_false heq
              have hne' : m'.val ≠ k := hne
              have hgt : k < m'.val := Nat.lt_of_le_of_ne hge' (Ne.symm hne')
              have hge_succ : k + 1 ≤ m'.val := hgt
              have hnlt_succ : ¬ m'.val < k + 1 := Nat.not_lt_of_le hge_succ
              rw [decide_eq_false hnlt_succ, Bool.false_and, Bool.false_and]
              rfl

/-- **HARD direction at arbitrary c**: every face cochain `v` with
    `∀ m, ψ_m(v) = false` lies in `InPrimaryCupSpanPlusBoundary c`.

    Constructed by aggregating all `c` layer-supported InPrimary
    cochains and showing pointwise equality with `v`. -/
theorem joint_psi_kernel_subset_primary (c : Nat) (v : EnrichedFaceVal c)
    (hv : ∀ m, psi_layer c m v = false) :
    InPrimaryCupSpanPlusBoundary c v := by
  apply InPrimaryCupSpanPlusBoundary.cong v
    (xor_aggregate c v c (Nat.le_refl c))
  · intro s t m'
    rw [xor_aggregate_val c v s t m' c (Nat.le_refl c)]
    rw [decide_eq_true m'.isLt, Bool.true_and]
  · exact xor_aggregate_in_primary c v hv c (Nat.le_refl c)

/-! ## §7 — Unconditional capstones

Now that both directions are closed at every `c` (EASY:
`primary_cup_span_soundness_all_c`; HARD: `joint_psi_kernel_subset_primary`),
the conditional `parametric_dual_span_capstone` becomes unconditional. -/

/-- **Joint ψ-kernel = `InPrimaryCupSpanPlusBoundary c`** at every c.
    Iff-version of the bidirectional containment. -/
theorem joint_psi_kernel_iff_primary (c : Nat) (v : EnrichedFaceVal c) :
    (∀ m, psi_layer c m v = false) ↔ InPrimaryCupSpanPlusBoundary c v :=
  ⟨joint_psi_kernel_subset_primary c v,
   fun h m => primary_cup_span_soundness_all_c c v h m⟩

/-- **Unconditional parametric dual-span** at every c.  The c
    ψ-discriminators `(ψ_0, …, ψ_{c-1})` span the dual of
    `EnrichedFaceVal c / InPrimaryCupSpanPlusBoundary c`, matching
    the parametric lower bound (`codim ≥ c`) and closing the
    `codim = c` upper bound for the PRIMARY cup-image. -/
theorem parametric_dual_span_unconditional (c : Nat) :
    ∀ v : EnrichedFaceVal c, ∃ b : Fin c → Bool,
      (∀ m, b m = psi_layer c m v)
      ∧ InPrimaryCupSpanPlusBoundary c (psi_residual c v)
      ∧ (∀ s t m', v s t m'
            = xor (weighted_e_sum c b s t m') (psi_residual c v s t m')) :=
  parametric_dual_span_capstone c (joint_psi_kernel_subset_primary c)

/-- **Unconditional codim upper bound** at every c: every face cochain
    `v` decomposes canonically modulo `InPrimaryCupSpanPlusBoundary c`
    into its `weighted_e_sum c (ψ-vector v)` representative. -/
theorem codim_upper_bound_unconditional (c : Nat) (v : EnrichedFaceVal c) :
    InPrimaryCupSpanPlusBoundary c (psi_residual c v)
    ∧ (∀ s t m', v s t m'
          = xor (weighted_e_sum c (fun m => psi_layer c m v) s t m')
                (psi_residual c v s t m')) :=
  codim_upper_bound_conditional c (joint_psi_kernel_subset_primary c) v

end E213.Lib.Math.Cohomology.Bipartite.V33EnrichedParametricDualSpanHardLift
