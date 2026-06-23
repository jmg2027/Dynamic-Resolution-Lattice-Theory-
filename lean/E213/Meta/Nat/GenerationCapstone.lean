import E213.Meta.Nat.UnitBox
import E213.Meta.Nat.UnitDistrib
import E213.Meta.Nat.UnitOrder
import E213.Meta.Nat.ProdCount

/-!
# The arithmetic-generation capstone

One citable theorem bundling the generation program: every law of the *ordered
commutative semiring* `(ℕ, +, ·, 0, 1, ≤)` is exhibited by a proof that **derives it
as the count-shadow of a unit-structure double-count** — `UnitList` / `UnitGrid` /
`UnitBox` / `UnitDistrib` / `UnitOrder` — *not* `Nat`'s own algebra. (Each component's
cone is verified free of the law it produces; see the individual files and
`theory/math/numbersystems/arithmetic_generation.md`.)

The capstone's *statements* are, extensionally, the ordinary `Nat` laws; its *content*
is that the witnesses are generated. The multiplicative count-Lens and the exact +/×
duality (`ProdCount`) are the companion result; unique factorization (FTA) is the open
frontier, requiring a non-structural multiplicative descent over *distinguishable*
prime atoms.
-/

namespace E213.Meta.Nat.GenerationCapstone

open E213.Meta.Nat.UnitList (fromNat add_comm_from_append add_assoc_from_append)
open E213.Meta.Nat.UnitGrid (mul_comm_from_grid)
open E213.Meta.Nat.UnitBox (mul_assoc_from_box)
open E213.Meta.Nat.UnitDistrib (mul_add_from_grid add_mul_from_grid)
open E213.Meta.Nat.UnitOrder (le_iff_unit_extension add_le_add_right)

/-- ★★★★★★★ **THE ARITHMETIC-GENERATION CAPSTONE.** The ordered commutative semiring
    `(ℕ, +, ·, 0, 1, ≤)` is generated: every law below is witnessed by a proof that
    derives it as the count-shadow of a unit-structure double-count (none presupposing
    the `Nat` law it produces). One object for "ℕ's arithmetic is forced by the shape
    of distinguishable/indistinguishable units, not authored." -/
theorem ordered_commutative_semiring_generated :
    -- additive monoid
    (∀ a b : Nat, a + b = b + a)
    ∧ (∀ a b c : Nat, (a + b) + c = a + (b + c))
    -- multiplicative monoid
    ∧ (∀ a b : Nat, a * b = b * a)
    ∧ (∀ a b c : Nat, (a * b) * c = a * (b * c))
    -- distributive bridges
    ∧ (∀ a b c : Nat, a * (b + c) = a * b + a * c)
    ∧ (∀ a b c : Nat, (a + b) * c = a * c + b * c)
    -- order, and its compatibility with +
    ∧ (∀ a b : Nat, a ≤ b ↔ ∃ l : List Unit, fromNat a ++ l = fromNat b)
    ∧ (∀ a b : Nat, a ≤ b → ∀ c, a + c ≤ b + c) :=
  ⟨add_comm_from_append,
   add_assoc_from_append,
   mul_comm_from_grid,
   mul_assoc_from_box,
   mul_add_from_grid,
   add_mul_from_grid,
   le_iff_unit_extension,
   fun _ _ h c => add_le_add_right h c⟩

end E213.Meta.Nat.GenerationCapstone
