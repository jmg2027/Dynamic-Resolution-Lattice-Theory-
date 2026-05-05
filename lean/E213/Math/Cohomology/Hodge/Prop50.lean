import E213.Math.Cohomology.Hodge.Star

import E213.Math.Cohomology.Cochain.Core
import E213.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 0) — Δ⁴ scalar cochain (trivial stratum)

Cochain 5 0 = Fin (binom 5 0) → Bool = Fin 1 → Bool, only 2
functions (constant true, constant false).  ⋆⋆ identity is
trivial via direct enumeration.

Closes the bottom stratum of the Hodge involution chain
(5, 0) → (5, 1) → (5, 2) → (5, 3) → (5, 4) over Δ⁴.
-/

namespace E213.Math.Cohomology.Hodge.Prop50

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)

open E213.Physics.Simplex.Counts (binom)

/-- Cochain 5 0 parametrized by 1 Bool value. -/
def pattern (b0 : Bool) : Cochain 5 0 :=
  fun _ => b0

/-- ⋆⋆ = id on every (5, 0) pattern (only 2 patterns). -/
theorem hodge_sq_pattern_5_0 :
    ∀ b0 : Bool, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 (pattern b0)) i = pattern b0 i := by
  decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 0, ⋆⋆σ = σ.

    Direct proof via Fin elimination — avoids `funext` to keep the
    statement at STRICT 0-AXIOM (no Quot.sound).  binom 5 0 = 1 so
    the only valid index is ⟨0, _⟩ where both sides reduce to σ ⟨0, _⟩
    by definition of hodgeStar. -/
theorem hodge_sq_prop_5_0 (σ : Cochain 5 0)
    (i : Fin (binom 5 0)) :
    hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i := by
  rcases i with ⟨val, hval⟩
  cases val with
  | zero => rfl
  | succ n =>
    have h : n + 1 < 1 := hval
    exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero n)

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 0). -/
theorem hodge_involution_capstone_5_0 :
    ∀ σ : Cochain 5 0, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i :=
  hodge_sq_prop_5_0

end E213.Math.Cohomology.Hodge.Prop50
