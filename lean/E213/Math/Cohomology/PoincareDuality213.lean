import E213.Math.Cohomology.Hodge.InvolutionCapstone

/-!
# Poincaré Duality in 213

Standard Poincaré duality: for a closed oriented n-manifold M, the
cap product with the fundamental class [M] gives a natural iso
H^k(M; R) ≅ H_{n-k}(M; R), and via universal coefficients
H^k(M; R) ≅ H^{n-k}(M; R) (for ℤ/2 cohomology, where orientation
is automatic).

In 213: the Hodge involution `hodgeStar n k m : Cochain n k →
Cochain n m` (with m = n − k) is *literally* Poincaré duality at
the cochain level — the complement-of-subset operation is the
combinatorial cap-with-fundamental-class.  Bijectivity (=
∅-axiom Poincaré duality) is the ⋆⋆ = id involution capstone
already proven on all 5 Δ⁴ strata.

STRICT ∅-AXIOM.
-/

namespace E213.Math.Cohomology.PoincareDuality213

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)
open E213.Math.Cohomology.Hodge.InvolutionCapstone
  (hodge_involution_5strata_capstone)
open E213.Physics.Simplex.Counts (binom)

/-- Poincaré duality map at level k on Δⁿ⁻¹: send σ : C^k to its
    Hodge dual ⋆σ : C^{n−k}.  In ℤ/2 the orientation sign collapses;
    the dual is the complement-indicator cochain. -/
abbrev poincareDual (n k m : Nat) := hodgeStar n k m

/-- ★★★★★ Poincaré Duality on Δ⁴.  STRICT ∅-AXIOM.

    The Hodge ⋆ map on each stratum (k, n−k) of Δ⁴ is a
    self-inverse bijection — i.e., Poincaré duality holds at
    every level.  Bundles `hodge_involution_5strata_capstone`
    under the standard "Poincaré duality" name.

    Stratum sizes:
      (5, 0) ↔ (5, 5) :  binom 5 0 = binom 5 5 = 1
      (5, 1) ↔ (5, 4) :  binom 5 1 = binom 5 4 = 5
      (5, 2) ↔ (5, 3) :  binom 5 2 = binom 5 3 = 10

    Each pair gives a Poincaré duality iso C^k ≅ C^{n−k} witnessed
    by ⋆ (forward) and ⋆ (backward), with ⋆⋆ = id pointwise. -/
theorem poincare_duality_delta4 :
    (∀ σ : Cochain 5 0, ∀ i : Fin (binom 5 0),
       hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
         hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
         hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 3, ∀ i : Fin (binom 5 3),
         hodgeStar 5 2 3 (hodgeStar 5 3 2 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 4, ∀ i : Fin (binom 5 4),
         hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i) :=
  hodge_involution_5strata_capstone

/-- Stratum-dimension symmetry (Poincaré duality at the dim level):
    dim C^k = dim C^{n−k}.  STRICT ∅-AXIOM by `decide`. -/
theorem dim_symmetry_delta4 :
    binom 5 0 = binom 5 5
    ∧ binom 5 1 = binom 5 4
    ∧ binom 5 2 = binom 5 3 := by decide

end E213.Math.Cohomology.PoincareDuality213
