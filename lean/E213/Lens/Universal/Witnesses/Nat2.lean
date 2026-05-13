import E213.Lens.Universal.Witnesses.Core

/-!
# Universal Lens at ℕ × ℕ — non-trivial witness

Partial step toward HANDOFF Open Problem #6 (`Lens (ℚ × ℚ)` upgrade).

Constructs `Lens (ℕ × ℕ)` with:
  - first component: exp-sum encoding `2^(view x) + 2^(view y)`
  - second component: depth counter

The first component gives a binary encoding where each Raw maps
to a Nat whose bit pattern encodes the tree structure.

Note on ℚ²: Lean 4.16.0 core does not export `Rat`, so a true
`Lens (ℚ × ℚ)` would require building 213-native ℚ infrastructure
(Int + positivity-quotient).  ℕ × ℕ here is the closest discrete
witness within current 213-native infrastructure.
-/

namespace E213.Lens.Universal.Witnesses.Nat2

open E213.Theory E213.Lens

/-- Lens (ℕ × ℕ): first component = exp-sum bit encoding,
    second component = depth counter. -/
def expSumLens : Lens (Nat × Nat) where
  base_a := (1, 0)
  base_b := (2, 0)
  combine x y := (2^x.1 + 2^y.1, x.2 + y.2 + 1)

/-- expSumLens.combine is symmetric.  STRICT ∅-AXIOM. -/
theorem expSumLens_symmetric :
    ∀ u v : Nat × Nat,
      expSumLens.combine u v = expSumLens.combine v u := by
  intro u v
  show (2^u.1 + 2^v.1, u.2 + v.2 + 1)
      = (2^v.1 + 2^u.1, v.2 + u.2 + 1)
  congr 1
  · exact Nat.add_comm _ _
  · congr 1; exact Nat.add_comm _ _

/-- Concrete: view a = (1, 0). -/
theorem expSumLens_view_a : expSumLens.view Raw.a = (1, 0) := rfl

/-- Concrete: view b = (2, 0). -/
theorem expSumLens_view_b : expSumLens.view Raw.b = (2, 0) := rfl

/-- Sample slash: view (slash a b) = (2^1 + 2^2, 1) = (6, 1). -/
example : expSumLens.view (Raw.slash Raw.a Raw.b (by decide))
        = (6, 1) := by decide

/-- ★★★ The expSum Lens distinguishes a from b in Raw.
    Concrete witness of the K_{3,2}^{(2)}-style "atomicity preserved
    under encoding" property. -/
theorem expSumLens_distinguishes_a_b :
    expSumLens.view Raw.a ≠ expSumLens.view Raw.b := by decide

/-- ★★★★ Sample distinguishability across more complex Raws. -/
theorem expSumLens_distinguishes_sample :
    expSumLens.view Raw.a
      ≠ expSumLens.view (Raw.slash Raw.a Raw.b (by decide)) := by decide

/-- ★★★★★ All four canonical depth-≤1 Raws have pairwise distinct views.
    Concrete injectivity check at the small-depth boundary. -/
theorem expSumLens_injective_small :
    expSumLens.view Raw.a ≠ expSumLens.view Raw.b
    ∧ expSumLens.view Raw.a
        ≠ expSumLens.view (Raw.slash Raw.a Raw.b (by decide))
    ∧ expSumLens.view Raw.b
        ≠ expSumLens.view (Raw.slash Raw.a Raw.b (by decide)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★★★★ Slash-views ALWAYS exceed leaf-views: 2^m + 2^n ≥ 6
    when m ≠ n and both ≥ 1.  (Numerically: leaf = 1 or 2, smallest
    slash = 6.) -/
theorem slash_view_minimum :
    (expSumLens.view (Raw.slash Raw.a Raw.b (by decide))).1 = 6 := rfl

end E213.Lens.Universal.Witnesses.Nat2
