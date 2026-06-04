/-!
# `Meta.Tactic.BoolHelper` — shared `Bool` lemmas (∅-axiom)

213-native helpers for `Bool` that are repeatedly needed across
`Lib/Math/NumberSystems/Real213/`, `Lib/Math/Analysis/`, and downstream cut/sum
machinery.  This module is the canonical source for the shared
`Bool` lemmas (`bool_eq_iff`, `xor_comm`, `eq_of_xor_false`,
`and_eq_true_pair`).

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Tactic.BoolHelper

/-- `a = b` iff `a = true ↔ b = true`.  Used in `Cut*` files whose
    underlying `Nat → Nat → Bool` arguments are compared by their
    truth-set logical content. -/
theorem bool_eq_iff (a b : Bool) (h : a = true ↔ b = true) :
    a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- `xor` is commutative on `Bool`.  213-native case-split proof
    (avoids `Bool.xor_comm`'s `simp`-based core proof, which can
    leak `propext`).  Used by `Lens.Instances.Parity` and other
    fold-swap-symmetric Lens constructions. -/
theorem xor_comm : ∀ u v : Bool, xor u v = xor v u := by
  intro u v; cases u <;> cases v <;> rfl

/-- `xor a b = false → a = b` (∅-axiom).  Reads the kernel condition
    `δ⁰ σ = 0` as vertex equality across an edge. -/
theorem eq_of_xor_false {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

/-- `(a && b) = true → a = true ∧ b = true` (∅-axiom `Bool` destructor;
    avoids cross-tier imports for conjunction splitting). -/
theorem and_eq_true_pair : ∀ {a b : Bool},
    (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => by cases h
  | true, false, h => by cases h

end E213.Tactic.BoolHelper
