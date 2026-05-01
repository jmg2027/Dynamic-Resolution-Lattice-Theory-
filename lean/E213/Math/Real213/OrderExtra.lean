import E213.Math.Real213.Order

/-!
# Research.Real213OrderExtra: equiv compatibility of le/lt (part of B5)

Part of Phase B5 of `E1_real213_analysis_roadmap.md` — algebraic
compatibility with equiv.  Only the order side here (arithmetic is separate).

## Results

- `le_of_equiv` : r ~ r' → r ≤ r'.
- `lt_implies_not_equiv` : r < r' → ¬ (r ~ r').

These are the first step in showing le/lt is *equivalence-relation compatible*.
-/

namespace E213.Math.Real213.OrderExtra

open E213.Firmware E213.Hypervisor
open E213.Math.Modulus.HasModulus
open E213.Hypervisor.Lens.Instances.AB
open E213.Math.Cauchy.Archimedean

/-- equiv → le. -/
theorem le_of_equiv (r r' : Real213) (h : Real213.equiv r r') : le r r' := by
  intro m k hk
  obtain ⟨N, hN⟩ := h m k hk
  refine ⟨N, fun i hi h_r' => ?_⟩
  rw [hN i hi]
  exact h_r'

/-- equiv → reverse le. -/
theorem ge_of_equiv (r r' : Real213) (h : Real213.equiv r r') : le r' r :=
  le_of_equiv r' r (equiv_symm r r' h)

/-- Incompatibility of lt and equiv — the core of strict order. -/
theorem lt_implies_not_equiv (r r' : Real213) :
    lt r r' → ¬ Real213.equiv r r' := by
  intro hlt hequiv
  obtain ⟨m, k, hk, N1, hN1⟩ := hlt
  obtain ⟨N2, hN2⟩ := hequiv m k hk
  let i := max N1 N2
  obtain ⟨ht, hf⟩ := hN1 i (Nat.le_max_left N1 N2)
  have he := hN2 i (Nat.le_max_right N1 N2)
  rw [he] at ht
  rw [ht] at hf
  exact Bool.noConfusion hf

/-- **Antisymmetry**: r ≤ r' ∧ r' ≤ r → r ~ r'.  Constructive Bool case-analysis. -/
theorem equiv_of_le_le (r r' : Real213) :
    le r r' → le r' r → Real213.equiv r r' := by
  intro h1 h2 m k hk
  obtain ⟨N1, hN1⟩ := h1 m k hk
  obtain ⟨N2, hN2⟩ := h2 m k hk
  refine ⟨max N1 N2, fun i hi => ?_⟩
  have hi1 : i ≥ N1 := Nat.le_trans (Nat.le_max_left N1 N2) hi
  have hi2 : i ≥ N2 := Nat.le_trans (Nat.le_max_right N1 N2) hi
  cases h : orderProj m k (abLens.view (r.xs i)) <;>
    cases h' : orderProj m k (abLens.view (r'.xs i))
  · rfl
  · have := hN1 i hi1 h'
    rw [h] at this
    exact Bool.noConfusion this
  · have := hN2 i hi2 h
    rw [h'] at this
    exact Bool.noConfusion this
  · rfl

end E213.Math.Real213.OrderExtra
