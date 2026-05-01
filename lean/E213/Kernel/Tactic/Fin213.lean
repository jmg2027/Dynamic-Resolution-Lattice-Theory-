/-!
# 213-native `Fin` helpers (∅-axiom)

Replacements for Lean-core `Fin.*` constructs that bring `propext`
into downstream theorems.

Two known leaks (see `AXIOM_FREE_STATUS.md`):

  - `Fin.elim0` — Lean-core proof brings `propext`.
  - `(0 : Fin (n+1))` literal — `OfNat` instance for `Fin` brings
    `propext`.  Use explicit `⟨0, Nat.zero_lt_succ _⟩` instead;
    no helper needed (it's already a term).

Companion to `Nat213.lean`.
-/

namespace E213.Tactic.Fin213

/-- ∅-axiom replacement for `Fin.elim0`. -/
def absurd0 {α : Sort _} (h : Fin 0) : α :=
  absurd h.isLt (Nat.not_lt_zero h.val)

end E213.Tactic.Fin213
