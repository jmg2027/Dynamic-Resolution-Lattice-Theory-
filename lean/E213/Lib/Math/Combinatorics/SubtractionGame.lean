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

/-! ## The Sprague–Grundy value — mex *is* the `GAP` instruction

The win/loss split above refines to the full **Grundy value** (the *nimber* the
game compiles to): `grundy n = mex {grundy of each option}`, where `mex` (minimal
excludant) is the least natural the option-set does **not** contain.  `mex` is
exactly the proof-ISA `GAP` instruction read by "least": the un-covered surplus
of a finite reading, pointed at by its smallest witness.  Sprague–Grundy theory
is then "every impartial game **compiles** to a nimber via iterated `GAP`," and
two games with equal Grundy value are interchangeable — a `READ`/`COMPILE`
universality, the game-theoretic face of the ISA. -/

/-- `mex` of a two-element option set `{a, b}`: the least `k ∈ {0,1,2}` with
    `k ≠ a` and `k ≠ b` (two options cannot block all of `0,1,2`).  This is the
    `GAP` instruction at finite scale — the least value the reading misses. -/
def mexPair (a b : Nat) : Nat :=
  if a ≠ 0 ∧ b ≠ 0 then 0
  else if a ≠ 1 ∧ b ≠ 1 then 1
  else 2

/-- The **Grundy value** (nimber) of the `S={1,2}` subtraction game: the mex of
    the options' Grundy values.  `grundy n = 0` ⟺ P-position. -/
def grundy : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => mexPair (grundy (n + 1)) (grundy n)

/-- ★★★★★★ **Sprague–Grundy value of the subtraction game**: the game compiles
    to the nimber `n mod 3` — `grundy (3q) = 0`, `grundy (3q+1) = 1`,
    `grundy (3q+2) = 2`.  Each step is one `mex` (= `GAP`) on the previous two
    concrete nimbers.  (Grundy `= 0` recovers the P-positions above.) -/
theorem grundy_values : ∀ q,
    grundy (3 * q) = 0 ∧ grundy (3 * q + 1) = 1 ∧ grundy (3 * q + 2) = 2
  | 0 => by decide
  | (q + 1) => by
      obtain ⟨h0, h1, h2⟩ := grundy_values q
      refine ⟨?_, ?_, ?_⟩
      · show mexPair (grundy (3 * q + 2)) (grundy (3 * q + 1)) = 0
        rw [h2, h1]; decide
      · show mexPair (mexPair (grundy (3 * q + 2)) (grundy (3 * q + 1)))
                     (grundy (3 * q + 2)) = 1
        rw [h2, h1]; decide
      · show mexPair (mexPair (mexPair (grundy (3 * q + 2)) (grundy (3 * q + 1)))
                             (grundy (3 * q + 2)))
                     (mexPair (grundy (3 * q + 2)) (grundy (3 * q + 1))) = 2
        rw [h2, h1]; decide

end E213.Lib.Math.Combinatorics.SubtractionGame
