import E213.Math.Cohomology.Dyadic.Signature

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

/-- Predicate: vertex is on S-side. -/
def isS (v : Fin 5) : Prop := v.val < 3

/-- Predicate: vertex is on T-side. -/
def isT (v : Fin 5) : Prop := v.val ≥ 3

/-- nextVertex value bound for S-side input. -/
private theorem nextVertex_S_val (v : Fin 5) (hv : v.val < 3) (b : Bool) :
    (nextVertex v b).val ≥ 3 := by
  obtain ⟨n, hn⟩ := v
  match n, hn, hv, b with
  | 0, _, _, false => show (3 : Nat) ≥ 3; omega
  | 0, _, _, true  => show (4 : Nat) ≥ 3; omega
  | 1, _, _, false => show (3 : Nat) ≥ 3; omega
  | 1, _, _, true  => show (4 : Nat) ≥ 3; omega
  | 2, _, _, false => show (3 : Nat) ≥ 3; omega
  | 2, _, _, true  => show (4 : Nat) ≥ 3; omega

/-- nextVertex value bound for T-side input. -/
private theorem nextVertex_T_val (v : Fin 5) (hv : v.val ≥ 3) (b : Bool) :
    (nextVertex v b).val < 3 := by
  obtain ⟨n, hn⟩ := v
  match n, hn, hv, b with
  | 0, _, h, _ => exact absurd h (by show ¬ (0 : Nat) ≥ 3; omega)
  | 1, _, h, _ => exact absurd h (by show ¬ (1 : Nat) ≥ 3; omega)
  | 2, _, h, _ => exact absurd h (by show ¬ (2 : Nat) ≥ 3; omega)
  | 3, _, _, false => show (0 : Nat) < 3; omega
  | 3, _, _, true  => show (1 : Nat) < 3; omega
  | 4, _, _, false => show (1 : Nat) < 3; omega
  | 4, _, _, true  => show (2 : Nat) < 3; omega

/-- nextVertex from S-side leads to T-side. -/
theorem nextVertex_S_to_T (v : Fin 5) (hv : isS v) (b : Bool) :
    isT (nextVertex v b) := nextVertex_S_val v hv b

/-- nextVertex from T-side leads to S-side. -/
theorem nextVertex_T_to_S (v : Fin 5) (hv : isT v) (b : Bool) :
    isS (nextVertex v b) := nextVertex_T_val v hv b

/-- ★★★ Bipartite alternation: signature at even steps is S-side,
    odd steps is T-side. -/
theorem signature_bipartite_alternation (bs : Nat → Bool) (k : Nat) :
    (k % 2 = 0 → isS (signature bs k))
    ∧ (k % 2 = 1 → isT (signature bs k)) := by
  induction k with
  | zero => exact ⟨fun _ => by show (0 : Nat) < 3; decide,
                   fun h => absurd h (by decide)⟩
  | succ k' ih =>
    refine ⟨?_, ?_⟩
    · intro hpar
      -- k' + 1 even ⇒ k' odd ⇒ sig k' on T-side ⇒ sig (k'+1) on S-side
      have hk' : k' % 2 = 1 := by omega
      exact nextVertex_T_to_S (signature bs k') (ih.2 hk') (bs k')
    · intro hpar
      have hk' : k' % 2 = 0 := by omega
      exact nextVertex_S_to_T (signature bs k') (ih.1 hk') (bs k')

end E213.Math.Cohomology.Dyadic.SignatureBipartite
