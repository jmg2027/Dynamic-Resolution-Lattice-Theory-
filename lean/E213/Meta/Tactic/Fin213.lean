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

/-- `Fin n`-pair encoding bound: `b · n + c < n²` for any `b, c : Fin n`.
    Used by base-`n` block encoding (`Fin (n²) ≅ Fin n × Fin n`). -/
theorem pair_encoded_lt {n : Nat} (b c : Fin n) :
    b.val * n + c.val < n * n := by
  have hb : b.val + 1 ≤ n := b.isLt
  have hc : c.val < n := c.isLt
  have hsucc : (b.val + 1) * n = b.val * n + n := Nat.succ_mul _ _
  have hbound : (b.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hb
  calc b.val * n + c.val
      < b.val * n + n := Nat.add_lt_add_left hc _
    _ = (b.val + 1) * n := hsucc.symm
    _ ≤ n * n := hbound

/-- ∅-axiom `Fin` equality from equal values (subst on values + proof
    irrelevance; avoids the `Fin.ext` `propext` leak). -/
theorem fin_eq_of_val (n : Nat) (a b : Nat)
    (ha : a < n) (hb : b < n) (h : a = b) :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := by
  subst h; rfl

end E213.Tactic.Fin213
