import E213.Math.Cohomology.Dyadic.Signature
import E213.Math.NatHelpers.AddMod213

/-!
# K_{3,2}^{(2)} signature bipartite alternation invariant

The K_{3,2}^{(2)} graph has 3 S-vertices {0, 1, 2} and 2
T-vertices {3, 4}.  Bipartite means edges only connect S to T.

`nextVertex` respects this — every transition flips between
S-side and T-side.  Therefore the signature trajectory:
  - sig 0 = ⟨0⟩ (S-side)
  - sig at even step → S-side (val < 3)
  - sig at odd step  → T-side (val ≥ 3)

This is the formal statement of bipartite alternation.
-/

namespace E213.Math.Cohomology.Dyadic.SignatureBipartite

open E213.Math.Cohomology.Dyadic.Signature (nextVertex signature)

/-- Predicate: vertex is on S-side. -/
def isS (v : Fin 5) : Prop := v.val < 3

/-- Predicate: vertex is on T-side. -/
def isT (v : Fin 5) : Prop := v.val ≥ 3

/-- Helper: ¬ k+3 < 3.  ∅-axiom. -/
private theorem not_succ_succ_succ_lt_three (k : Nat) : ¬ k + 3 < 3 :=
  Nat.not_succ_le_zero _ ∘ Nat.le_of_succ_le_succ ∘
  Nat.le_of_succ_le_succ ∘ Nat.le_of_succ_le_succ

/-- nextVertex value bound for S-side input.  STRICT ∅-AXIOM. -/
private theorem nextVertex_S_val (v : Fin 5) (hv : v.val < 3) (b : Bool) :
    (nextVertex v b).val ≥ 3 := by
  obtain ⟨n, hn⟩ := v
  match n, hn, hv, b with
  | 0, _, _, false => exact Nat.le_refl _
  | 0, _, _, true  => exact Nat.le_succ _
  | 1, _, _, false => exact Nat.le_refl _
  | 1, _, _, true  => exact Nat.le_succ _
  | 2, _, _, false => exact Nat.le_refl _
  | 2, _, _, true  => exact Nat.le_succ _
  | k+3, _, h, _ => exact absurd h (not_succ_succ_succ_lt_three k)

/-- Helper: ¬ 3 ≤ k for k ∈ {0, 1, 2}.  ∅-axiom. -/
private theorem not_three_le_zero : ¬ 3 ≤ 0 := by decide
private theorem not_three_le_one : ¬ 3 ≤ 1 := by decide
private theorem not_three_le_two : ¬ 3 ≤ 2 := by decide

/-- nextVertex value bound for T-side input.  STRICT ∅-AXIOM. -/
private theorem nextVertex_T_val (v : Fin 5) (hv : v.val ≥ 3) (b : Bool) :
    (nextVertex v b).val < 3 := by
  obtain ⟨n, hn⟩ := v
  match n, hn, hv, b with
  | 0, _, h, _ => exact absurd h not_three_le_zero
  | 1, _, h, _ => exact absurd h not_three_le_one
  | 2, _, h, _ => exact absurd h not_three_le_two
  | 3, _, _, false => exact (by decide : (0 : Nat) < 3)
  | 3, _, _, true  => exact (by decide : (1 : Nat) < 3)
  | 4, _, _, false => exact (by decide : (1 : Nat) < 3)
  | 4, _, _, true  => exact (by decide : (2 : Nat) < 3)
  | _+5, hn, _, _ =>
    exact absurd hn (Nat.not_succ_le_zero _ ∘ Nat.le_of_succ_le_succ ∘
                     Nat.le_of_succ_le_succ ∘ Nat.le_of_succ_le_succ ∘
                     Nat.le_of_succ_le_succ ∘ Nat.le_of_succ_le_succ)

/-- nextVertex from S-side leads to T-side. -/
theorem nextVertex_S_to_T (v : Fin 5) (hv : isS v) (b : Bool) :
    isT (nextVertex v b) := nextVertex_S_val v hv b

/-- nextVertex from T-side leads to S-side. -/
theorem nextVertex_T_to_S (v : Fin 5) (hv : isT v) (b : Bool) :
    isS (nextVertex v b) := nextVertex_T_val v hv b

/-- Helper: (k+1) % 2 reduces to (k%2 + 1) % 2 via add_mod_left. -/
private theorem succ_mod_two (k : Nat) : (k + 1) % 2 = (k % 2 + 1) % 2 :=
  E213.Math.NatHelpers.AddMod213.add_mod_left (by decide : 0 < 2) k 1

/-- Helper: (k+1) % 2 = 0 → k % 2 = 1.  STRICT ∅-AXIOM. -/
private theorem succ_mod2_zero_imp {k : Nat} (h : (k + 1) % 2 = 0) :
    k % 2 = 1 := by
  have hkmod : k % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [succ_mod_two] at h
  -- h : (k%2 + 1) % 2 = 0, hkmod : k%2 < 2, so k%2 ∈ {0, 1}
  rcases Nat.lt_or_ge (k % 2) 1 with h0 | h1
  · -- k%2 = 0, then (0+1)%2 = 1 ≠ 0
    have : k % 2 = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ h0)
    rw [this] at h; exact absurd h (by decide)
  · -- k%2 ≥ 1 and k%2 < 2, so k%2 = 1
    exact Nat.le_antisymm (Nat.le_of_lt_succ hkmod) h1

/-- Helper: (k+1) % 2 = 1 → k % 2 = 0.  STRICT ∅-AXIOM. -/
private theorem succ_mod2_one_imp {k : Nat} (h : (k + 1) % 2 = 1) :
    k % 2 = 0 := by
  have hkmod : k % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [succ_mod_two] at h
  rcases Nat.lt_or_ge (k % 2) 1 with h0 | h1
  · exact Nat.le_zero.mp (Nat.le_of_lt_succ h0)
  · have : k % 2 = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hkmod) h1
    rw [this] at h; exact absurd h (by decide)

/-- ★★★ Bipartite alternation: signature at even steps is S-side,
    odd steps is T-side.  STRICT ∅-AXIOM. -/
theorem signature_bipartite_alternation (bs : Nat → Bool) (k : Nat) :
    (k % 2 = 0 → isS (signature bs k))
    ∧ (k % 2 = 1 → isT (signature bs k)) := by
  induction k with
  | zero => exact ⟨fun _ => (by decide : (0 : Nat) < 3),
                   fun h => absurd h (by decide)⟩
  | succ k' ih =>
    refine ⟨?_, ?_⟩
    · intro hpar
      exact nextVertex_T_to_S (signature bs k')
        (ih.2 (succ_mod2_zero_imp hpar)) (bs k')
    · intro hpar
      exact nextVertex_S_to_T (signature bs k')
        (ih.1 (succ_mod2_one_imp hpar)) (bs k')

end E213.Math.Cohomology.Dyadic.SignatureBipartite
