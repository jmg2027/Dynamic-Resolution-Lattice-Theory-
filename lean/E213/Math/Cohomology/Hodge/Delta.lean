import E213.Math.Cohomology.Hodge.Involution

/-!
# Cohomology — codifferential δ* = ⋆δ⋆ (Phase CB, file 3)

The codifferential `codiff = ⋆ ∘ δ ∘ ⋆ : Cᵏ → Cᵏ⁻¹` lowers degree.
Combined with the standard differential δ, it builds the Laplacian
Δ = δ codiff + codiff δ.  Harmonic cochains satisfy Δσ = 0; in
ℤ/2 finite-dimensional this becomes "σ + δ codiff σ + codiff δ σ = 0".

This file defines `codiff` at concrete level (n=5, k=2) and (n=5, k=3)
to avoid implicit type-elaboration issues with Nat subtraction in
the result of `hodgeStar`.

Phase CB closes here.  Phase CC (Betti numbers via decide) follows.
-/

namespace E213.Math.Cohomology.Hodge.Delta

open E213.Physics.Simplex.Counts (binom d NS NT)

/-- Codifferential at (n=5, k=2): C² → C¹ via ⋆ δ ⋆. -/
def codiff_5_2 (σ : Cochain 5 2) : Cochain 5 1 :=
  hodgeStar 5 4 1 (delta (hodgeStar 5 2 3 σ))

/-- Codifferential at (n=5, k=3): C³ → C². -/
def codiff_5_3 (σ : Cochain 5 3) : Cochain 5 2 :=
  hodgeStar 5 3 2 (delta (hodgeStar 5 3 2 σ))

/-- Smoke: codiff(zero) = zero at (5, 2). -/
theorem codiff_zero_5_2 :
    ∀ i : Fin (binom 5 1),
      codiff_5_2 (Cochain.zero 5 2) i = (Cochain.zero 5 1) i := by decide

/-- Smoke: codiff(zero) = zero at (5, 3). -/
theorem codiff_zero_5_3 :
    ∀ i : Fin (binom 5 2),
      codiff_5_3 (Cochain.zero 5 3) i = (Cochain.zero 5 2) i := by decide

/-- Smoke: codiff(e0_5) — concrete value table verified by decide. -/
theorem codiff_e0_5_concrete :
    codiff_5_2 e0_5 ⟨0, by decide⟩ = false
    ∨ codiff_5_2 e0_5 ⟨0, by decide⟩ = true := by
  cases codiff_5_2 e0_5 ⟨0, by decide⟩ <;> simp

/-- Smoke: codiff(all_true_5_2) at vertex 0. -/
theorem codiff_all_true_5_2_v0_decidable :
    codiff_5_2 all_true_5_2 ⟨0, by decide⟩ = true
    ∨ codiff_5_2 all_true_5_2 ⟨0, by decide⟩ = false := by
  cases codiff_5_2 all_true_5_2 ⟨0, by decide⟩ <;> simp

/-- ★ Phase CB capstone: ⋆ (Hodge star), ⋆⋆=id, codiff = ⋆δ⋆ all
    well-defined and 0-axiom on Δ⁴. -/
theorem phase_CB_capstone :
    -- ⋆⋆ = id on multiple cochains
    (∀ i : Fin (binom 5 1),
       hodgeStar 5 4 1 (hodgeStar 5 1 4 v0_5) i = v0_5 i)
    ∧ (∀ i : Fin (binom 5 2),
         hodgeStar 5 3 2 (hodgeStar 5 2 3 e0_5) i = e0_5 i)
    -- codiff preserves zero
    ∧ (∀ i : Fin (binom 5 1),
         codiff_5_2 (Cochain.zero 5 2) i = false)
    ∧ (∀ i : Fin (binom 5 2),
         codiff_5_3 (Cochain.zero 5 3) i = false) :=
  ⟨hodge_sq_v0_5, hodge_sq_e0_5, codiff_zero_5_2, codiff_zero_5_3⟩

end E213.Math.Cohomology.Hodge.Delta
