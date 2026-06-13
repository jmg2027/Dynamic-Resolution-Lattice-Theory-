import E213.Meta.Nat.PureNat
import E213.Meta.Nat.PowBasic
import E213.Meta.Nat.UnitGrid
import E213.Meta.Nat.UnitList
import E213.Meta.Nat.UnitHyper

/-!
# HyperAssoc — what arises at `^`: the dimension axis (and its algebra shadows)

The unit-object floor builds one new structure per rung, each **adjoining a
dimension** (`simplicial_operation_tower.md` L1/L5):

* `+` — the 1-D unit **list** (`UnitList`): the count *is* the order, so `+`
  commutes (`UnitList.add_comm_from_append`) and brackets freely
  (`Nat.add_assoc`);
* `×` — the 2-D unit **grid** (`UnitGrid`): the transpose double-count makes
  `×` commute (`UnitGrid.mul_comm_from_grid`) and brackets freely
  (`PureNat.mul_assoc`);
* `^` — the `b`-D unit **grid** (`UnitHyper`): `count (hcube a b) = a^b`, with
  the base read as a **side** (a length) and the exponent as a **dimension**
  (an axis count) — **two different-typed readouts** (`count_eq_side_pow_dim`).

Read positively, `^` **adjoins the dimension-setting axis** — the new
degree-of-freedom (`DOF = rung − 2 = 1`).  The base sets each axis's side; the
exponent sets *how many axes* there are.  They are different *types* (a length
vs a dimension-count), so they do not interchange — and the **algebraic
defects below are the count *shadows*** of that type-asymmetry, not the rung's
mechanism:

* **`aᵇ ≠ bᵃ`** (`pow_not_comm`) is the count shadow of a **dimension swap**:
  `hcube 2 3` is 3-dimensional, `hcube 3 2` is 2-dimensional
  (`UnitHyper.swap_changes_dim`), so their cell counts `2^3` and `3^2` differ
  (`pow_not_comm_is_dim_shadow`).  Swapping side↔dimension builds a
  *different-dimensional* object; "commutativity" only ever read the count.
* **`(2^2)^3 ≠ 2^(2^3)`** (`pow_not_assoc`): the bracketing selects *which*
  index is the dimension and which the side, so the two bracketings build
  different cubes — the tree returns as genuine structure once base and
  exponent live in different dimensions.

The one **associativity-shaped law `^` keeps**, `(aᵇ)ᶜ = a^(b·c)`
(`pow_surviving` = `PowBasic.pow_mul_pure`), does **not** close `^` over itself
(`(aᵇ)ᶜ ≠ a^(bᶜ)`); it **linearizes the dimension back down to `×`** on the
exponent — stacking `c` axes of `b` axes is `b·c` axes — which is why the tower
flattens *one rung down*.

The **bracket-blindness** reading (`bracket_blind_iff_assoc`): an operation is
associative ⟺ the two bracketings of every triple agree.  `+` and `×` are
bracketing-blind (no index plays a distinguished role); `^` is not, witnessed
by `64 ≠ 256`.

All ∅-axiom.  The concrete witnesses use `decide` on closed Nat (in)equalities
(reduces through `Nat.decEq`, stays pure — *not* a finite ∀-Bool `decide`,
which would pull `Quot.sound`).
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

/-! ## 3. ★★ The dimension axis — the algebra defects are its count shadows -/

/-- Bare arithmetic witness for non-commutativity: `2^3 = 8 ≠ 9 = 3^2`. -/
theorem pow_not_comm_concrete : (2:Nat)^3 ≠ 3^2 := by decide

/-- Bare arithmetic witness for non-associativity: the two bracketings
    of `2^2^3` disagree — `(2^2)^3 = 64 ≠ 256 = 2^(2^3)`. -/
theorem pow_not_assoc_concrete : ((2:Nat)^2)^3 ≠ 2^(2^3) := by decide

/-- ★ `^` is **not commutative**: base and exponent set *different types* — a
    side (length) vs a dimension (axis count) — so they do not interchange,
    witnessed by `2^3 ≠ 3^2`.  Read positively, this is `pow_not_comm_is_dim_shadow`:
    the count shadow of a dimension swap. -/
theorem pow_not_comm : ¬ Comm (· ^ ·) := by
  intro h
  exact pow_not_comm_concrete (h 2 3)

/-- ★ `^` is **not associative**: the two bracketings of `2^2^3` build
    different cubes — the bracketing selects which index is the dimension —
    so `(2^2)^3 = 64 ≠ 256 = 2^(2^3)`. -/
theorem pow_not_assoc : ¬ Assoc (· ^ ·) := by
  intro h
  exact pow_not_assoc_concrete (h 2 2 3)

/-- ★★ **`aᵇ ≠ bᵃ` is the count shadow of a dimension swap.**  The cube
    `hcube 2 3` is 3-dimensional and `hcube 3 2` is 2-dimensional
    (`UnitHyper.swap_changes_dim`); they are *different-dimensional objects*,
    and their unit-cell counts (`UnitHyper.count_hcube`) are exactly `2^3` and
    `3^2`, which differ.  So non-commutativity is not "a law lost" — it is the
    count reading of side and exponent being different *types*. -/
theorem pow_not_comm_is_dim_shadow :
    E213.Meta.Nat.UnitHyper.count (E213.Meta.Nat.UnitHyper.hcube 2 3)
      ≠ E213.Meta.Nat.UnitHyper.count (E213.Meta.Nat.UnitHyper.hcube 3 2) := by
  rw [E213.Meta.Nat.UnitHyper.count_hcube, E213.Meta.Nat.UnitHyper.count_hcube]
  exact pow_not_comm_concrete

/-! ## 4. ★ The dimension linearizes back to `×` on the exponent -/

/-- ★ The **only** associativity-shaped law `^` keeps: `(aᵇ)ᶜ = a^(b·c)`
    (= `PowBasic.pow_mul_pure`, reassembled).  It does **not** close `^`
    over itself — contrast `pow_not_assoc`, `(aᵇ)ᶜ ≠ a^(bᶜ)` in general
    (`2^(2^3) = 256 ≠ 64 = (2^2)^3`).  Instead it **linearizes the dimension
    down to `×` on the exponent** — stacking `c` axes of `b` axes is `b·c`
    axes — which is why the tower flattens one rung down. -/
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
