import E213.Meta.Nat.PureNat
import E213.Meta.Nat.PowBasic
import E213.Meta.Nat.UnitGrid
import E213.Meta.Nat.UnitList

/-!
# HyperAssoc — the wall: associativity AND commutativity die together at `^`

The append-floor (`UnitList`, `UnitGrid`) hands the tower two structural
gifts at once.  **Associativity** is the bracketing the floor never had:
a list `[u,u,…]` carries no tree, so concatenation forgets bracketing for
free — `append` is associative for *any* element type.  **Commutativity**
is the order-on-units the floor cannot record: indistinguishable units
carry no position, so arrangement is no information to forget
(`UnitList.append_comm`), and `UnitGrid` lifts the same forgetting one
rung up to `×` via the grid transpose (`mul_comm_from_grid`).

The tower carries **both** gifts through `×`:

* `+` is associative (`Nat.add_assoc`, the floor's bracketing-blindness)
  and commutative (`UnitList.add_comm_from_append`, the shadow of
  unit-list append commutativity);
* `×` is associative (`PureNat.mul_assoc`) and commutative
  (`UnitGrid.mul_comm_from_grid`, the grid transpose double-count).

`^` is the first rung that loses **both at once**:

* **non-commutative** — `2^3 = 8 ≠ 9 = 3^2`.  Where the floor's units
  were indistinguishable (and `×`'s grid cells were too), `^` is iterated
  `×`, and base vs exponent are *distinguishable* roles: the tree the
  floor discarded returns as the asymmetry `aᵇ ≠ bᵃ`
  (`pow_not_comm`).
* **non-associative** — `(2^2)^3 = 64 ≠ 256 = 2^(2^3)`.  The two
  bracketings of `2^2^3` disagree, so the bracketing/tree the floor
  forgot is back as genuine information (`pow_not_assoc`).

So `×` is the **last assoc+comm rung**.

The **surviving ghost** of associativity is `(aᵇ)ᶜ = a^(b·c)`
(`pow_surviving` = `PowBasic.pow_mul_pure`): the only
associativity-shaped law `^` keeps does **not** close `^` over itself
(`(aᵇ)ᶜ ≠ a^(bᶜ)` in general) — it linearizes `^` back down to `×` on
the exponent.  That is why the hyperoperation tower flattens *one rung
down*: associativity, when it survives at all, survives only as a law
that drops `^` to `×`, never `^` to `^`.

The **bracket-blindness** view (`bracket_blind_iff_assoc`): an operation
is associative ⟺ the two bracketings of every triple agree.  `+` and `×`
are bracketing-blind; `^` is not, witnessed by `64 ≠ 256`.

All ∅-axiom.  The negative witnesses use `decide` on closed concrete Nat
(in)equalities (reduces through `Nat.decEq`, stays pure — *not* a finite
∀-Bool `decide`, which would pull `Quot.sound`).
-/

namespace E213.Meta.Nat.HyperAssoc

open E213.Meta.Nat.PureNat (mul_assoc)
open E213.Meta.Nat.UnitList (add_comm_from_append)
open E213.Meta.Nat.UnitGrid (mul_comm_from_grid)
open E213.Meta.Nat.PowBasic (pow_mul_pure)

/-! ## 1. Abstract predicates -/

/-- A binary operation is **associative** when bracketing never matters. -/
def Assoc (f : Nat → Nat → Nat) : Prop := ∀ a b c, f (f a b) c = f a (f b c)

/-- A binary operation is **commutative** when order never matters. -/
def Comm (f : Nat → Nat → Nat) : Prop := ∀ a b, f a b = f b a

/-! ## 2. The survival ladder — `+` and `×` keep both gifts -/

/-- `+` is associative: the floor's bracketing-blindness (`Nat.add_assoc`
    is pure). -/
theorem add_is_assoc : Assoc (· + ·) := fun a b c => Nat.add_assoc a b c

/-- `+` is commutative: the shadow of unit-list append commutativity
    (`UnitList.add_comm_from_append`). -/
theorem add_is_comm : Comm (· + ·) := fun a b => add_comm_from_append a b

/-- `×` is associative: pure `PureNat.mul_assoc`. -/
theorem mul_is_assoc : Assoc (· * ·) := fun a b c => mul_assoc a b c

/-- `×` is commutative: the grid transpose double-count
    (`UnitGrid.mul_comm_from_grid`). -/
theorem mul_is_comm : Comm (· * ·) := fun a b => mul_comm_from_grid a b

/-! ## 3. ★★ The wall — `^` loses both -/

/-- Bare arithmetic witness for non-commutativity: `2^3 = 8 ≠ 9 = 3^2`. -/
theorem pow_not_comm_concrete : (2:Nat)^3 ≠ 3^2 := by decide

/-- Bare arithmetic witness for non-associativity: the two bracketings
    of `2^2^3` disagree — `(2^2)^3 = 64 ≠ 256 = 2^(2^3)`. -/
theorem pow_not_assoc_concrete : ((2:Nat)^2)^3 ≠ 2^(2^3) := by decide

/-- ★ `^` is **not commutative**: base and exponent are distinguishable
    roles, witnessed by `2^3 ≠ 3^2`.  The tree the floor discarded
    returns as `aᵇ ≠ bᵃ`. -/
theorem pow_not_comm : ¬ Comm (· ^ ·) := by
  intro h
  exact pow_not_comm_concrete (h 2 3)

/-- ★ `^` is **not associative**: the two bracketings of `2^2^3`
    disagree, `(2^2)^3 = 64 ≠ 256 = 2^(2^3)`.  The bracketing/tree the
    floor forgot is back as genuine information. -/
theorem pow_not_assoc : ¬ Assoc (· ^ ·) := by
  intro h
  exact pow_not_assoc_concrete (h 2 2 3)

/-! ## 4. ★ The surviving ghost of associativity -/

/-- ★ The **only** associativity-shaped law `^` keeps: `(aᵇ)ᶜ = a^(b·c)`
    (= `PowBasic.pow_mul_pure`, reassembled).  It does **not** close `^`
    over itself — contrast `pow_not_assoc`, `(aᵇ)ᶜ ≠ a^(bᶜ)` in general
    (`2^(2^3) = 256 ≠ 64 = (2^2)^3`).  Instead it linearizes `^` down to
    `×` on the exponent, which is why the tower flattens one rung down. -/
theorem pow_surviving (a b c : Nat) : (a ^ b) ^ c = a ^ (b * c) :=
  (pow_mul_pure a b c).symm

/-- The surviving law is genuinely **not** `(aᵇ)ᶜ = a^(bᶜ)`: the
    `×`-linearized bracketing and the `^`-closed bracketing disagree,
    `(2^2)^3 = 64 ≠ 256 = 2^(2^3)`.  (Same witness as `pow_not_assoc`,
    stated against the surviving law to make the contrast explicit.) -/
theorem pow_surviving_not_self : ((2:Nat) ^ 2) ^ 3 ≠ 2 ^ (2 ^ 3) :=
  pow_not_assoc_concrete

/-! ## 5. The bracket-blindness bridge

An operation is associative ⟺ the two bracketings of any triple agree —
which is `Assoc` definitionally.  `+` and `×` are bracketing-blind; `^`
is not, witnessed by `64 ≠ 256`. -/

/-- An operation is bracketing-blind on every triple exactly when it is
    associative (definitional unfolding of `Assoc`). -/
theorem bracket_blind_iff_assoc (f : Nat → Nat → Nat) :
    (∀ a b c, f (f a b) c = f a (f b c)) ↔ Assoc f := Iff.rfl

/-- `+` is bracketing-blind. -/
theorem add_bracket_blind : ∀ a b c : Nat, (a + b) + c = a + (b + c) := add_is_assoc

/-- `×` is bracketing-blind. -/
theorem mul_bracket_blind : ∀ a b c : Nat, (a * b) * c = a * (b * c) := mul_is_assoc

/-- `^` is **not** bracketing-blind, witnessed by `(2^2)^3 = 64 ≠ 256 =
    2^(2^3)` — the bracketing returns as information. -/
theorem pow_not_bracket_blind : ¬ (∀ a b c : Nat, (a ^ b) ^ c = a ^ (b ^ c)) := by
  intro h
  exact pow_not_assoc_concrete (h 2 2 3)

end E213.Meta.Nat.HyperAssoc
