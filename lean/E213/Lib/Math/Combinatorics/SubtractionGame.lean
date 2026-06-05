import E213.Meta.Tactic.NatHelper

/-!
# Combinatorial game theory: the subtraction game S = {1,2} (∅-axiom)

A genuinely different domain — impartial combinatorial games (Sprague–Grundy) —
where the proof is **backward induction on the game tree**, not an algebraic
identity.

Rules: a position is a pile of `n` tokens; a move removes `1` or `2`; the player
who cannot move (`n = 0`) loses.  `gLoss n = true` means the player *to move*
from `n` **loses** (a P-position), computed by backward induction:
`gLoss n` is `true` iff *every* legal move lands on a position the opponent wins.

**Theorem (Bouton-style):** the P-positions are exactly the **multiples of 3** —
the Sprague–Grundy 3-periodicity.  Cross-domain: game value ↔ modular arithmetic.
The proof is the period-3 structure of the game tree (`period`), not a ring
identity.
-/

namespace E213.Lib.Math.Combinatorics.SubtractionGame

/-- `gLoss n = true` ⟺ the player to move from `n` loses (P-position).
    Backward induction: lose iff every move (to `n−1`, `n−2`) lands on a win. -/
def gLoss : Nat → Bool
  | 0 => true
  | 1 => false
  | (n + 2) => !(gLoss (n + 1)) && !(gLoss n)

/-- No two consecutive positions are both P-positions (a P-position has a move
    to it, making the predecessor an N-position). -/
theorem consec : ∀ n, (gLoss n && gLoss (n + 1)) = false
  | 0 => rfl
  | (n + 1) => by
      show (gLoss (n + 1) && (!(gLoss (n + 1)) && !(gLoss n))) = false
      cases gLoss (n + 1) <;> rfl

/-- ★★★★★ **The game value is 3-periodic** — the Sprague–Grundy periodicity of
    the subtraction game, by backward induction on the tree. -/
theorem period (n : Nat) : gLoss (n + 3) = gLoss n := by
  show (!(!(gLoss (n + 1)) && !(gLoss n)) && !(gLoss (n + 1))) = gLoss n
  have hc := consec n
  cases hp : gLoss (n + 1) <;> cases hq : gLoss n <;>
    first
      | rfl
      | (rw [hp, hq] at hc; exact absurd hc (by decide))

/-- Multiples of 3 are P-positions: `gLoss (3q) = true`. -/
theorem gLoss_three_mul : ∀ q, gLoss (3 * q) = true
  | 0 => rfl
  | (q + 1) => by
      rw [Nat.mul_succ]
      show gLoss (3 * q + 3) = true
      rw [period]; exact gLoss_three_mul q

/-- `3q + 1` is an N-position: `gLoss (3q+1) = false`. -/
theorem gLoss_three_mul_add_one : ∀ q, gLoss (3 * q + 1) = false
  | 0 => rfl
  | (q + 1) => by
      rw [Nat.mul_succ]
      show gLoss (3 * q + 1 + 3) = false
      rw [period]; exact gLoss_three_mul_add_one q

/-- `3q + 2` is an N-position: `gLoss (3q+2) = false`. -/
theorem gLoss_three_mul_add_two : ∀ q, gLoss (3 * q + 2) = false
  | 0 => rfl
  | (q + 1) => by
      rw [Nat.mul_succ]
      show gLoss (3 * q + 2 + 3) = false
      rw [period]; exact gLoss_three_mul_add_two q

/-- ★★★★★★ **P-positions of the subtraction game S = {1,2} are exactly the
    multiples of 3** (the complete Sprague–Grundy characterization): the residue
    of `n` mod 3 decides win/loss — `3q` lose, `3q+1` and `3q+2` win. -/
theorem subtraction_game_characterization (q : Nat) :
    gLoss (3 * q) = true
    ∧ gLoss (3 * q + 1) = false
    ∧ gLoss (3 * q + 2) = false :=
  ⟨gLoss_three_mul q, gLoss_three_mul_add_one q, gLoss_three_mul_add_two q⟩

end E213.Lib.Math.Combinatorics.SubtractionGame
