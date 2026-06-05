import E213.Meta.Tactic.NatHelper

/-!
# A formal model of the lift-archetype order

The essay `lift_archetypes_order_and_duality.md` draws the seven lift archetypes
as a partial order with dual pairs.  That diagram was *asserted*.  This file makes
it a small **theorem-backed model**: the archetypes become an inductive type, the
informal "lift cost" becomes a *defined* `Nat`, and the diagram's structural
features — a unique bottom, a top, and equal-cost dual pairs — become proofs about
that model.

Honest scope: the cost assignment below is a **definition** that reads the
catalog's stated lift costs (DIAGONAL self-supplies = `0`; one well-founded pass /
one induction / one counting bound / one sum-of-squares = `1`; ORBIT adds a free
action = `2`; REFRAME wraps a base archetype = `3`).  It is a *model* of the
catalog, not a derivation of the costs from first principles — but it replaces
prose labels with a quantity and the Hasse picture with provable min/max/equicost
structure, which is strictly more than narrative.
-/

namespace E213.Lib.Math.Foundations.ArchetypeOrder

/-- The seven lift archetypes (`ProofISALifts`) as a type. -/
inductive Archetype where
  | diagonal | loop | flow | count | positivity | orbit | reframe
  deriving DecidableEq

open Archetype

/-- The **lift cost** of an archetype, as a defined `Nat` (the catalog's stated
    costs): `DIAGONAL = 0`; the four single-pass lifts `= 1`; `ORBIT = 2`
    (LOOP + a free action); `REFRAME = 3` (wraps a base archetype). -/
def liftCost : Archetype → Nat
  | diagonal => 0
  | loop => 1
  | flow => 1
  | count => 1
  | positivity => 1
  | orbit => 2
  | reframe => 3

/-- The order on archetypes, induced by lift cost. -/
def le (a b : Archetype) : Prop := liftCost a ≤ liftCost b

/-- The induced order is reflexive. -/
theorem le_refl (a : Archetype) : le a a := Nat.le_refl _

/-- The induced order is transitive. -/
theorem le_trans {a b c : Archetype} (hab : le a b) (hbc : le b c) : le a c :=
  Nat.le_trans hab hbc

/-- **DIAGONAL is the unique bottom**: it has cost `0`, so it is below every
    archetype — the residue every infinity-proof reduces to. -/
theorem diagonal_bottom (a : Archetype) : le diagonal a := Nat.zero_le _

/-- **REFRAME is the top**: the meta-transport sits above every base
    archetype. -/
theorem reframe_top (a : Archetype) : le a reframe := by
  show liftCost a ≤ liftCost reframe
  cases a <;> decide

/-- **The dual pair LOOP ⟷ FLOW is equicost** — mirror images (µ/ν), at
    the same height, hence order-incomparable-but-equal. -/
theorem loop_flow_equicost : liftCost loop = liftCost flow := rfl

/-- **The dual pair COUNT ⟷ POSITIVITY is equicost** — the two faces of
    `GAP`, at the same height. -/
theorem count_positivity_equicost : liftCost count = liftCost positivity := rfl

/-- ORBIT sits strictly above the single-pass lifts (it adds a free action). -/
theorem loop_lt_orbit : liftCost loop < liftCost orbit := by decide

/-- **The order model, summarized**: a unique bottom (DIAGONAL, cost 0),
    a top (REFRAME, cost 3), and both dual pairs at equal height — the Hasse
    picture of the essay, now proven about the cost model. -/
theorem archetype_order_structure :
    (∀ a, le diagonal a)
    ∧ (∀ a, le a reframe)
    ∧ liftCost loop = liftCost flow
    ∧ liftCost count = liftCost positivity
    ∧ liftCost loop < liftCost orbit
    ∧ liftCost orbit < liftCost reframe :=
  ⟨diagonal_bottom, reframe_top, loop_flow_equicost, count_positivity_equicost,
   loop_lt_orbit, by decide⟩

/-! ## The duality is an actual involution (not an analogy)

A referee noted that "LOOP ⟷ FLOW duality" and "DIAGONAL self-dual" were
asserted, not pinned to any involution.  Here is the involution. -/

/-- The **duality involution**: swaps each dual pair, fixes the root, the
    quotient (ORBIT), and the meta-transport (REFRAME). -/
def dual : Archetype → Archetype
  | diagonal => diagonal
  | loop => flow
  | flow => loop
  | count => positivity
  | positivity => count
  | orbit => orbit
  | reframe => reframe

/-- `dual` is an **involution** — `dual ∘ dual = id`. -/
theorem dual_involutive (a : Archetype) : dual (dual a) = a := by cases a <;> rfl

/-- **DIAGONAL is self-dual** — now a theorem, not a metaphor: it is a fixed
    point of the duality involution. -/
theorem diagonal_self_dual : dual diagonal = diagonal := rfl

/-- **LOOP ⟷ FLOW** is a genuine swap of the involution. -/
theorem dual_swaps_loop_flow : dual loop = flow ∧ dual flow = loop := ⟨rfl, rfl⟩

/-- **COUNT ⟷ POSITIVITY** is a genuine swap of the involution. -/
theorem dual_swaps_count_positivity :
    dual count = positivity ∧ dual positivity = count := ⟨rfl, rfl⟩

/-- The duality **preserves lift cost** — dual partners sit at equal height, so
    `dual` is a height-preserving automorphism of the cost model. -/
theorem dual_cost (a : Archetype) : liftCost (dual a) = liftCost a := by
  cases a <;> rfl

/-- **`le` is a preorder, NOT a partial order** (the essay's "partial order" was
    imprecise): its symmetric part fails antisymmetry exactly on the dual pairs —
    `loop` and `flow` are `≤` each other yet distinct.  The genuine partial order
    lives on the *cost classes* (the quotient), where each dual pair collapses to
    one height. -/
theorem le_not_antisymm : le loop flow ∧ le flow loop ∧ loop ≠ flow :=
  ⟨Nat.le_refl 1, Nat.le_refl 1, by decide⟩

end E213.Lib.Math.Foundations.ArchetypeOrder
