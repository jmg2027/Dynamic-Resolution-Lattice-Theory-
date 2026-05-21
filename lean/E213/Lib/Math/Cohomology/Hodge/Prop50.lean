import E213.Lib.Math.Cohomology.Hodge.Star

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# ⋆⋆ = id Prop-lift at (5, 0) — Δ⁴ scalar cochain (trivial stratum)

Cochain 5 0 = Fin (binom 5 0) → Bool = Fin 1 → Bool, only 2
functions (constant true, constant false).  ⋆⋆ identity is
trivial via direct enumeration.

Closes the bottom stratum of the Hodge involution chain
(5, 0) → (5, 1) → (5, 2) → (5, 3) → (5, 4) over Δ⁴.
-/

namespace E213.Lib.Math.Cohomology.Hodge.Prop50

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar)

open E213.Lib.Physics.Simplex.Counts (binom)

/-- ★★★ Universal ⋆⋆=id Prop-lift capstone at (5, 0).

    Direct proof via Fin elimination — avoids `funext` to keep the
    statement at STRICT 0-AXIOM (no Quot.sound).  binom 5 0 = 1 so
    the only valid index is ⟨0, _⟩ where both sides reduce to σ ⟨0, _⟩
    by definition of hodgeStar. -/
theorem hodge_involution_capstone_5_0 :
    ∀ σ : Cochain 5 0, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i := by
  intro σ i
  rcases i with ⟨val, hval⟩
  cases val with
  | zero => rfl
  | succ n =>
    have h : n + 1 < 1 := hval
    exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero n)

end E213.Lib.Math.Cohomology.Hodge.Prop50
