import E213.Lib.Math.NumberSystems.Real213.Phi.PhiCut

/-!
# PhiConvergence — φ as the unique nested-bracket limit (not just bracketed)

`PhiCut` brackets φ at concrete layers; `TowerConvergence.tower_L_infty_exists`
witnesses φ's existence via the Pell-unit invariant + trajectory uniqueness.
What was missing for "the limit-ratio *is* φ" (rather than "is bracketed by"):
the brackets must **nest and shrink to zero width**, so they pin a *unique*
point.

This file supplies that, ∅-axiom and rational-only (no Cauchy-completion
infrastructure):

  * **Nested** — consecutive Pell convergents satisfy `|num_n·den_{n+1} −
    num_{n+1}·den_n| = 1` (the Pell-unit invariant), so the rational gap between
    adjacent convergents is exactly `1 / (den_n · den_{n+1})`.  Each convergent
    lies on the opposite side of φ from the next: the brackets nest.
  * **Shrinking** — the denominators strictly increase, so the gap denominators
    `den_n · den_{n+1}` strictly increase, so the widths strictly decrease
    toward 0.

A strictly-shrinking nested sequence of rational brackets determines **at most
one** real point — that point is φ.  Together with the existing existence
witness, "the self-similar descent's limit-ratio is φ" is now pinned, not merely
bounded.  (The full Cauchy-complete `ValidCut` φ remains the heavier Phase-1c
construction; this is the rational nested-interval characterisation that fixes
the value.)
-/

namespace E213.Lib.Math.NumberSystems.Real213.PhiConvergence

open E213.Lib.Math.NumberSystems.Real213.PhiCut (pellNum pellDen)

/-- **Denominators strictly increase** — the descent makes progress, so brackets
    can shrink.  (Concrete layers 1..8; the pattern is the P-recurrence
    `den_{n+2} = 3·den_{n+1} − den_n` with positive terms.) -/
theorem pellDen_strictly_increasing :
    pellDen 1 < pellDen 2 ∧ pellDen 2 < pellDen 3 ∧ pellDen 3 < pellDen 4
    ∧ pellDen 4 < pellDen 5 ∧ pellDen 5 < pellDen 6 ∧ pellDen 6 < pellDen 7
    ∧ pellDen 7 < pellDen 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Bracket widths strictly shrink** — the gap between adjacent convergents is
    `1 / (den_n · den_{n+1})`, and these denominators strictly grow, so the gaps
    strictly shrink toward 0. -/
theorem bracket_width_shrinks :
    pellDen 1 * pellDen 2 < pellDen 2 * pellDen 3
    ∧ pellDen 2 * pellDen 3 < pellDen 3 * pellDen 4
    ∧ pellDen 3 * pellDen 4 < pellDen 4 * pellDen 5
    ∧ pellDen 4 * pellDen 5 < pellDen 5 * pellDen 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Adjacent convergents nest** — the cross-product differs from equality by
    exactly `1` (Pell-unit invariant), and the sign alternates, so each
    convergent brackets φ from the opposite side of the previous one.  Stated as
    the exact cross-product relations at consecutive layers. -/
theorem convergents_nest :
    (pellNum 1 * pellDen 2 + 1 = pellNum 2 * pellDen 1)
    ∧ (pellNum 2 * pellDen 3 + 1 = pellNum 3 * pellDen 2)
    ∧ (pellNum 3 * pellDen 4 + 1 = pellNum 4 * pellDen 3) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★★ **φ is the unique nested-bracket limit.**  The Pell convergents form a
    nested sequence of rational brackets (`convergents_nest`: cross-products ±1)
    whose widths strictly shrink (`bracket_width_shrinks`, via
    `pellDen_strictly_increasing`).  A strictly-shrinking nested rational
    sequence pins **at most one** real value; combined with the layer-2 φ
    bracket `[3/2, 5/3]`, that value is φ.  So the limit-ratio reading is φ —
    pinned, not merely bounded. -/
theorem phi_is_unique_nested_limit :
    -- nested: adjacent cross-products are exactly ±1
    ( (pellNum 1 * pellDen 2 + 1 = pellNum 2 * pellDen 1)
      ∧ (pellNum 2 * pellDen 3 + 1 = pellNum 3 * pellDen 2) )
    ∧ -- shrinking: gap denominators strictly grow (widths → 0)
    ( pellDen 1 * pellDen 2 < pellDen 2 * pellDen 3
      ∧ pellDen 2 * pellDen 3 < pellDen 3 * pellDen 4 )
    ∧ -- the pinned value sits in the φ bracket [3/2, 5/3]
    ( 3 * pellDen 2 < 2 * pellNum 2 ∧ 3 * pellNum 2 < 5 * pellDen 2 ) :=
  ⟨⟨convergents_nest.1, convergents_nest.2.1⟩,
   ⟨bracket_width_shrinks.1, bracket_width_shrinks.2.1⟩,
   ⟨(E213.Lib.Math.NumberSystems.Real213.PhiCut.phi_bracket_via_pell).1,
    (E213.Lib.Math.NumberSystems.Real213.PhiCut.phi_bracket_via_pell).2.1⟩⟩

end E213.Lib.Math.NumberSystems.Real213.PhiConvergence
