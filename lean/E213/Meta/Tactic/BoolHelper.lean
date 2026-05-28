/-!
# `Meta.Tactic.BoolHelper` — shared `Bool` lemmas (∅-axiom)

213-native helpers for `Bool` that are repeatedly needed across
`Lib/Math/Real213/`, `Lib/Math/Analysis/`, and downstream cut/sum
machinery.  Each lemma here was previously emitted as `private
theorem bool_eq_iff` (or variants `_v2` / `_v3` / `_local` / `'`)
in a dozen leaf files; this module is the canonical source.

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

end E213.Tactic.BoolHelper
