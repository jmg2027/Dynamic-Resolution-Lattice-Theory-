import E213.Theory.Raw.Endomorphic
import E213.Theory.Raw.Levels

/-!
# Theory.Raw.PrimitiveTower — the most primitive 213 tower

A "tower" is one arrow iterated.  The *most primitive* tower fixes
that arrow to the only one the Raw axiom provides — `slash`
(self-pointing) — and the seed to the first distinguishing `{a, b}`.
Nothing is added at any rung; "going up a level" is the residue
pointing at its previous pointing once more.

  `rawTower 0       = b`
  `rawTower (n + 1) = a / (rawTower n)`   (the left spine)

The single structural readout is the depth: it tracks the level
exactly (`rawTower_depth`), and the universal binary-tree invariant
`depth < leaves` (`Raw.depth_lt_leaves`) holds at every rung.  The
inhabitant *count* `2, 3, 5, 12, …` is a separate count-Lens reading
of the full depth-stratified Raw recurrence (`UniverseChain.RawRecurrence`),
not this single thread.

Every named tower (Cayley-Dickson, Cantor cardinality, …) is this
spine with `slash` replaced by a chosen step — i.e. a Lens reading
of this object (`theory/essays/synthesis/tower_atlas.md`).
-/

namespace E213.Theory.Raw.PrimitiveTower

open E213.Theory
open E213.Theory.Raw.Endomorphic (slashOrSelf slashOrSelf_of_ne)
open E213.Term.Internal (Tree)

/-- The two atoms differ — propext-free.  The `decide` path routes
    through `DecidableEq Raw`, which pulls `propext`; `Tree.noConfusion`
    on the underlying constructors does not. -/
theorem a_ne_b : Raw.a ≠ Raw.b :=
  fun h => Tree.noConfusion (congrArg Subtype.val h)

/-- The most primitive tower: iterate the single self-pointing arrow
    `slash` from the first distinguishing.  `slashOrSelf` is the total
    form of `slash`; it fires as a genuine `slash` at every rung
    because `a ≠ rawTower n` (proved in `depth_and_ne`). -/
def rawTower : Nat → Raw
  | 0     => Raw.b
  | n + 1 => slashOrSelf Raw.a (rawTower n)

/-- One rung adds exactly one level of depth (non-recursive step). -/
theorem depth_step (n : Nat) (hd : (rawTower n).depth = n)
    (hne : Raw.a ≠ rawTower n) : (rawTower (n + 1)).depth = n + 1 := by
  have hfire : rawTower (n + 1) = Raw.slash Raw.a (rawTower n) hne :=
    slashOrSelf_of_ne hne
  have hmax : max (0 : Nat) n = n :=
    (E213.Tactic.NatHelper.max_comm_pure 0 n).trans
      (E213.Tactic.NatHelper.max_eq_left_pure (Nat.zero_le n))
  rw [hfire, Raw.depth_slash Raw.a (rawTower n) hne,
      show Raw.depth Raw.a = 0 from rfl, hd, hmax, Nat.add_comm 1 n]

/-- `a` is never the next rung (non-recursive step). -/
theorem ne_step (n : Nat) (hd : (rawTower n).depth = n)
    (hne : Raw.a ≠ rawTower n) : Raw.a ≠ rawTower (n + 1) := by
  intro e
  have h0 : (0 : Nat) = n + 1 :=
    calc (0 : Nat) = Raw.depth Raw.a := rfl
      _ = (rawTower (n + 1)).depth := congrArg Raw.depth e
      _ = n + 1 := depth_step n hd hne
  exact Nat.noConfusion h0

/-- Depth tracks the level exactly, and `a` is never a rung — the
    `≠ a` fact is what lets each `slash` fire. -/
theorem depth_and_ne : ∀ n, (rawTower n).depth = n ∧ Raw.a ≠ rawTower n
  | 0 => ⟨rfl, a_ne_b⟩
  | n + 1 =>
      let ⟨hd, hne⟩ := depth_and_ne n
      ⟨depth_step n hd hne, ne_step n hd hne⟩

/-- ★ The spine's depth is its level. -/
theorem rawTower_depth (n : Nat) : (rawTower n).depth = n :=
  (depth_and_ne n).1

/-- ★ The universal binary-tree invariant on every rung. -/
theorem rawTower_lt_leaves (n : Nat) :
    (rawTower n).depth < (rawTower n).leaves :=
  Raw.depth_lt_leaves (rawTower n)

/-- ★★ Most-primitive-tower capstone: each rung adds exactly one
    level of depth, and `depth < leaves` never fails. -/
theorem primitive_tower_summary (n : Nat) :
    (rawTower n).depth = n ∧
    (rawTower n).depth < (rawTower n).leaves :=
  ⟨rawTower_depth n, rawTower_lt_leaves n⟩

end E213.Theory.Raw.PrimitiveTower
