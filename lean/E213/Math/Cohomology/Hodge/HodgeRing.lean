import E213.Math.Cohomology.Cup.Ring
import E213.Math.Cohomology.Hodge.Star
import E213.Math.Cohomology.Hodge.InvolutionCapstone

/-!
# Hodge Toolkit T4 — Hodge ring action (⋆ on cup product)

Cup-product / Hodge-star compatibility on Δ⁴ at concrete cochains.
The "Hodge ring" structure: H*(Δ⁴; ℤ/2) is graded-commutative
under ⌣ and admits the Hodge involution ⋆ : H^k → H^{n-k}.

All identities decided pointwise on Δ⁴; STRICT ∅-AXIOM.
-/

namespace E213.Math.Cohomology.Hodge.HodgeRing

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Cup.Core (cup all_true_5_1)
open E213.Math.Cohomology.Cup.Ring (unit_5)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)
open E213.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Physics.Simplex.Counts (binom)

/-- Hodge-paired cup at level (k, k → 2k → n−2k). -/
def hodgePair (n k : Nat) (σ τ : Cochain n k) : Cochain n (n - (k + k)) :=
  hodgeStar n (k + k) (n - (k + k)) (cup n k k σ τ)

/-- ⋆ of the multiplicative unit on Δ⁴: the top-dim fundamental
    class on C⁵ (= Fin 1 → Bool). -/
theorem hodgeStar_unit_5 :
    ∀ i : Fin (binom 5 5), hodgeStar 5 0 5 unit_5 i = true := by decide

/-- ⋆ of `all_true_5_1` is the all-true cochain on C⁴. -/
theorem hodgeStar_allTrue_5_1 :
    ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 all_true_5_1 i = true := by decide

/-- Ring identity 1·1 = 1. -/
theorem unit_cup_unit :
    cup 5 0 0 unit_5 unit_5 ⟨0, by decide⟩ = true := by decide

/-- ⋆(unit ⌣ unit) = top fundamental class. -/
theorem star_cup_unit :
    ∀ i : Fin (binom 5 5),
      hodgeStar 5 0 5 (cup 5 0 0 unit_5 unit_5) i = true := by decide

/-- ⋆ commutes with right-cup-by-unit on v0_5: ⋆(v0 ⌣ 1) = ⋆v0. -/
theorem star_cup_v0_unit_eq_star_v0 :
    ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 (cup 5 1 0 v0_5 unit_5) i = hodgeStar 5 1 4 v0_5 i := by
  decide

/-- ★★★★★ Hodge ring capstone — STRICT ∅-AXIOM. -/
theorem hodge_ring_capstone :
    (∀ i : Fin (binom 5 5), hodgeStar 5 0 5 unit_5 i = true)
    ∧ (∀ i : Fin (binom 5 4), hodgeStar 5 1 4 all_true_5_1 i = true)
    ∧ (cup 5 0 0 unit_5 unit_5 ⟨0, by decide⟩ = true)
    ∧ (∀ i : Fin (binom 5 5),
         hodgeStar 5 0 5 (cup 5 0 0 unit_5 unit_5) i = true)
    ∧ (∀ i : Fin (binom 5 4),
         hodgeStar 5 1 4 (cup 5 1 0 v0_5 unit_5) i = hodgeStar 5 1 4 v0_5 i) :=
  ⟨hodgeStar_unit_5, hodgeStar_allTrue_5_1, unit_cup_unit,
   star_cup_unit, star_cup_v0_unit_eq_star_v0⟩

end E213.Math.Cohomology.Hodge.HodgeRing
