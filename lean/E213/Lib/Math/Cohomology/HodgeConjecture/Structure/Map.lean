import E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone
import E213.Lib.Math.Cohomology.HodgeConjecture.Foundation.Conjecture

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Physics.Simplex.Counts
/-!
# Hodge Toolkit T5 — Hodge map ⋆ : H^k → H^{n-k}

The Hodge involution as a ℤ/2-linear bijection on Δ⁴ cochain
strata.  Lifts the all-stratum involution capstone to a packaged
"Hodge map" with explicit:

  * inverse map  (= ⋆ in the opposite direction; involution)
  * XOR-linearity (chain-level Hodge linearity)
  * zero ↦ zero  (algebraic-cycle preservation)

Establishes that ⋆ descends to a well-defined ℤ/2-linear bijection
H^k(Δ⁴) ≅ H^{4-k}(Δ⁴) on cohomology classes.  STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.HodgeConjecture.Structure.Map

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar complementIdx)
open E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone
  (hodge_involution_5strata_capstone)
open E213.Lib.Physics.Simplex.Counts (binom)

private theorem c_lt_5_1 :
    ∀ i : Fin (binom 5 4), complementIdx 5 4 i.val < binom 5 1 := by decide

/-- ⋆ : C¹(Δ⁴) → C⁴(Δ⁴) is its own pre-inverse (involution). -/
theorem hodge_bijection_5_1 (σ : Cochain 5 1) (i : Fin (binom 5 1)) :
    hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i :=
  hodge_involution_5strata_capstone.2.1 σ i

/-- ⋆ : C²(Δ⁴) → C³(Δ⁴) is its own pre-inverse. -/
theorem hodge_bijection_5_2 (σ : Cochain 5 2) (i : Fin (binom 5 2)) :
    hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i :=
  hodge_involution_5strata_capstone.2.2.1 σ i

/-- ⋆ sends zero cochain to zero cochain (in C⁴). -/
theorem hodgeStar_zero_5_1 :
    ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 (Cochain.zero 5 1) i = false := by decide

/-- ⋆ is XOR-linear at stratum (5,1).  STRICT ∅-AXIOM via
    `dif_pos` + Cochain.add unfolding. -/
theorem hodgeStar_xor_5_1 (σ τ : Cochain 5 1) (i : Fin (binom 5 4)) :
    hodgeStar 5 1 4 (Cochain.add σ τ) i
      = xor (hodgeStar 5 1 4 σ i) (hodgeStar 5 1 4 τ i) := by
  show (if h : complementIdx 5 4 i.val < binom 5 1 then
          (Cochain.add σ τ) ⟨complementIdx 5 4 i.val, h⟩ else false)
       = xor (if h : complementIdx 5 4 i.val < binom 5 1 then
                σ ⟨complementIdx 5 4 i.val, h⟩ else false)
             (if h : complementIdx 5 4 i.val < binom 5 1 then
                τ ⟨complementIdx 5 4 i.val, h⟩ else false)
  rw [dif_pos (c_lt_5_1 i), dif_pos (c_lt_5_1 i), dif_pos (c_lt_5_1 i)]
  rfl

/-- ★★★★★ Hodge map capstone — STRICT ∅-AXIOM.

    ⋆ is a ℤ/2-linear bijective involution on Δ⁴ cochains.
    Bundle:
      · ⋆⋆ = id at every stratum (k = 0..4) [from InvolutionCapstone]
      · ⋆ 0 = 0          (zero preservation, stratum (5,1))
      · ⋆ XOR-linear      (stratum (5,1)) -/
theorem hodge_map_capstone :
    (∀ σ : Cochain 5 1, ∀ i, hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i)
    ∧ (∀ i : Fin (binom 5 4), hodgeStar 5 1 4 (Cochain.zero 5 1) i = false)
    ∧ (∀ σ τ : Cochain 5 1, ∀ i,
         hodgeStar 5 1 4 (Cochain.add σ τ) i
           = xor (hodgeStar 5 1 4 σ i) (hodgeStar 5 1 4 τ i)) :=
  ⟨hodge_bijection_5_1, hodgeStar_zero_5_1, hodgeStar_xor_5_1⟩

end E213.Lib.Math.Cohomology.HodgeConjecture.Structure.Map
