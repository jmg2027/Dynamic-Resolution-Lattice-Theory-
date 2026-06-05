import E213.Meta.Tactic.NatHelper

/-!
# Two-heap Nim — the mirroring strategy (∅-axiom)

Nim with two heaps `(a, b)`: a move reduces one heap to a strictly smaller value;
the player who cannot move (`(0,0)`) loses.  **Bouton (1901), `n = 2`:** the
P-positions (player-to-move loses) are exactly the **balanced** positions `a = b`
— the *mirroring* strategy (whatever the opponent takes from one heap, copy it on
the other).

Rather than build the game-tree recursion, we certify `{a = b}` as the
P-position set directly by the standard P/N criterion:

  · **closed** — every move from a balanced position leaves it unbalanced
    (`nim2_closed_*`);
  · **progress** — from every unbalanced position some move reaches a balanced one
    (`nim2_progress`).

A set satisfying both *is* the set of P-positions of a finite impartial game, so
this is the complete characterization.

Cross-domain: game value ↔ equality of heap sizes (the `n=2` case of the nim-sum
`XOR = 0` law).  **General Bouton** (arbitrary heaps, P ⟺ nim-sum `= 0`) is the
open frontier: `research-notes/frontiers/nim_bouton/` — core `Nat.xor` lemmas are
`propext`/`Quot.sound`-dirty, so it needs a pure ∅-axiom XOR theory + the
highest-set-bit winning move.
-/

namespace E213.Lib.Math.Combinatorics.NimTwoHeap

/-- A two-heap position is **balanced** (a P-position) iff the heaps are equal. -/
def Balanced (a b : Nat) : Prop := a = b

/-- **Closed (left move)**: from a balanced position, reducing the first heap
    unbalances it — no move within the balanced set. -/
theorem nim2_closed_left (a b : Nat) (h : Balanced a b) :
    ∀ a', a' < a → ¬ Balanced a' b :=
  fun _ ha' he => absurd (he.trans h.symm) (Nat.ne_of_lt ha')

/-- **Closed (right move)**: reducing the second heap also unbalances it. -/
theorem nim2_closed_right (a b : Nat) (h : Balanced a b) :
    ∀ b', b' < b → ¬ Balanced a b' :=
  fun _ hb' he => absurd (he.symm.trans h) (Nat.ne_of_lt hb')

/-- ★★★★★ **Progress (the mirroring move)**: from any unbalanced position there
    is a move to a balanced one — take the larger heap down to the smaller. -/
theorem nim2_progress (a b : Nat) (h : ¬ Balanced a b) :
    (∃ a', a' < a ∧ Balanced a' b) ∨ (∃ b', b' < b ∧ Balanced a b') := by
  cases Nat.lt_or_ge a b with
  | inl hab => exact Or.inr ⟨a, hab, rfl⟩
  | inr hba =>
      have hlt : b < a := Nat.lt_of_le_of_ne hba (fun he => h he.symm)
      exact Or.inl ⟨b, hlt, rfl⟩

/-- ★★★★★★ **Two-heap Nim, fully characterized**: `{a = b}` is closed under all
    moves and reachable from every unbalanced position — hence it is exactly the
    P-position set.  The mirroring strategy, ∅-axiom. -/
theorem nim_two_heap_P_positions (a b : Nat) :
    (Balanced a b →
      (∀ a', a' < a → ¬ Balanced a' b) ∧ (∀ b', b' < b → ¬ Balanced a b'))
    ∧ (¬ Balanced a b →
      (∃ a', a' < a ∧ Balanced a' b) ∨ (∃ b', b' < b ∧ Balanced a b')) :=
  ⟨fun h => ⟨nim2_closed_left a b h, nim2_closed_right a b h⟩, nim2_progress a b⟩

end E213.Lib.Math.Combinatorics.NimTwoHeap
