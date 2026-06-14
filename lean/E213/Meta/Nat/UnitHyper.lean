import E213.Meta.Nat.PureNat
import E213.Meta.Nat.UnitList
import E213.Meta.Nat.UnitGrid

/-!
# UnitHyper — the rung-3 object for `^`: the `b`-dimensional unit grid

`UnitList` gave `+` from a 1-D list of indistinguishable units (the count is
the order, `add_comm_from_append`); `UnitGrid` gave `×` from the 2-D unit grid
(the transpose double-count, `mul_comm_from_grid`).  This file is the level-3
sibling: where the 1-D list gives `+` and the 2-D grid gives `×`, the
`b`-**dimensional** unit grid gives `^`.

The object is built generatively, **no numbers, no identity baked in** — the
layer rule (`simplicial_operation_tower.md` L1) applied once more: a
`(b+1)`-dimensional cube is `a` translated **copies** of the `b`-dimensional
cube, glued along a *new* axis.  Read positively (the methodological
principle of the frontier note): the rung **adjoins one dimension axis** — it
does not "lose commutativity".

  * `HCube` / `Forest` — a unit hypercube: indistinguishable unit **cells**
    nested into **boxes** (a box is a list of lower-dimensional cubes laid
    along one axis).  `Forest` is `List HCube` spelled out so the recursions
    are structural (no core `List` lemmas, no well-founded recursion).
  * `hcube a b` — the canonical `b`-dimensional cube of **side `a`**: `cell`
    at dimension `0`; `a` copies of the dimension-`b` cube at dimension `b+1`.
  * `count` — the unit-cell count.  **`count_hcube : count (hcube a b) = a ^ b`**
    (the cell-count readout — the `a^b` *shadow*, the analogue of
    `UnitGrid.total_rows : total (rows a b) = a * b`).
  * `count_hcube_succ` — the **generative climb**: `count (hcube a (b+1)) =
    a * count (hcube a b)` — each new dimension glues `a` copies, so `^` is
    `×`-iteration of the `×`-cube (the L1 "axis = previous layer" rule, on the
    object; `HyperLadder.hyperop_climb` at level 3 is its Nat readout).

The **positive twist — base and exponent are different types** (the thing
`HyperAssoc` framed negatively as "loses commutativity").  The one object
carries **two structural readouts of different type**:

  * `side` — a **length** (the base `a`): how many copies sit along an axis;
  * `dim` — a **dimension count** (the exponent `b`): how many axes there are.

and **`count = side ^ dim`** (`count_eq_side_pow_dim`).  `dim` climbs by exactly
`+1` per rung (`dim_hcube_succ` — the dilation/DOF axis *arising*), the count
pins each axis at the base.  Swapping side↔dimension swaps a *length* with a
*dimension-count*: it builds a **different-dimensional** object
(`dim (hcube 2 3) = 3 ≠ 2 = dim (hcube 3 2)`, `swap_changes_dim`), which is the
structural reason the *count* shadow reads `2^3 ≠ 3^2` — not a loss, a
type-mismatch.

All ∅-axiom; self-contained mutual recursion over `HCube`/`Forest` (no core
`List` lemmas, no `funext`/`Quot.sound`); the count readout uses only
`UnitList.count` and PURE-core `Nat.pow_succ`/`Nat.mul_comm`.
-/

namespace E213.Meta.Nat.UnitHyper

/-! ## The object: nested unit cells

`HCube` and `Forest` are mutually inductive so that "a box holds a list of
sub-cubes" is structural — `Forest` is exactly `List HCube`, written out so
the `count`/`dim` recursions compile without well-founded recursion or any
core `List` lemma. -/

mutual
  /-- A unit hypercube: a single `cell` (a dimension-`0` point — one
      indistinguishable unit), or a `box` of lower-dimensional cubes laid
      side by side along one axis. -/
  inductive HCube where
    | cell : HCube
    | box  : Forest → HCube
  /-- A forest = the sub-cubes along one axis (`List HCube`, inlined). -/
  inductive Forest where
    | nil  : Forest
    | cons : HCube → Forest → Forest
end

/-! ## The cell count (the readout to `a^b`) -/

mutual
  /-- The unit-cell count of a cube: a cell is one unit; a box totals its
      sub-cubes. -/
  def count : HCube → Nat
    | .cell  => 1
    | .box f => countF f
  /-- The cell count of a forest = sum over the sub-cubes. -/
  def countF : Forest → Nat
    | .nil      => 0
    | .cons c f => count c + countF f
end

/-! ## The two structural readouts: `dim` (axis count) and `side` (length) -/

mutual
  /-- The **dimension** of a cube = nesting depth = number of axes.  A cell
      has dimension `0`; a box adds one axis over its sub-cubes (read along
      the first one — uniform cubes agree on every child). -/
  def dim : HCube → Nat
    | .cell  => 0
    | .box f => 1 + dimF f
  /-- Dimension read off a forest's first sub-cube (`0` for an empty axis). -/
  def dimF : Forest → Nat
    | .nil      => 0
    | .cons c _ => dim c
end

/-- The **side** of a cube = how many copies sit along its top axis = the
    forest length (`1` for a bare cell, the degenerate dimension-`0` point). -/
def side : HCube → Nat
  | .cell  => 1
  | .box f => lenF f
where
  /-- Number of sub-cubes along one axis. -/
  lenF : Forest → Nat
    | .nil      => 0
    | .cons _ f => 1 + lenF f

/-! ## The canonical cube `hcube a b` (side `a`, dimension `b`) -/

/-- `a` copies of a cube `c`, laid along one new axis (a forest). -/
def hcubeF (c : HCube) : Nat → Forest
  | 0     => .nil
  | a + 1 => .cons c (hcubeF c a)

/-- The canonical **`b`-dimensional unit cube of side `a`**.  Dimension `0` is
    a single cell (`a^0 = 1`, the point); dimension `b+1` glues **`a` copies**
    of the dimension-`b` cube along a new axis (the layer rule, L1). -/
def hcube (a : Nat) : Nat → HCube
  | 0     => .cell
  | b + 1 => .box (hcubeF (hcube a b) a)

/-! ## The cell-count readout: `count (hcube a b) = a ^ b` -/

/-- `a` copies of `c` total `a · count c` cells (bare induction on the copy
    count — the analogue of `UnitGrid.total_rows`'s per-row sum). -/
theorem countF_hcubeF (c : HCube) : ∀ a, countF (hcubeF c a) = a * count c
  | 0     => by show 0 = 0 * count c; rw [Nat.zero_mul]
  | a + 1 => by
      show count c + countF (hcubeF c a) = (a + 1) * count c
      rw [countF_hcubeF c a, Nat.succ_mul, Nat.add_comm]

/-- ★★ **The cell-count is `a^b`** — the `^`-readout (the shadow): the
    `b`-dimensional cube of side `a` has `a^b` unit cells.  The dimension-`b+1`
    cube is `a` copies of the dimension-`b` cube (`count_hcube_succ`), so the
    count multiplies by `a` at each rung: `a^{b+1} = a · a^b`.  Analogue of
    `UnitGrid.total_rows : total (rows a b) = a * b`, one dimension up. -/
theorem count_hcube : ∀ (a b : Nat), count (hcube a b) = a ^ b
  | _, 0     => rfl
  | a, b + 1 => by
      show countF (hcubeF (hcube a b) a) = a ^ (b + 1)
      rw [countF_hcubeF (hcube a b) a, count_hcube a b, Nat.pow_succ, Nat.mul_comm]

/-- ★ **The generative climb (positive L1 rule).**  Each new dimension glues
    `a` copies of the previous cube, so the cell count multiplies by `a`:
    `count (hcube a (b+1)) = a · count (hcube a b)`.  This is `^` *as*
    `×`-iteration of the `×`-cube — read on the object, not as the Nat
    identity `a^{b+1} = a·a^b` (that is the count shadow). -/
theorem count_hcube_succ (a b : Nat) :
    count (hcube a (b + 1)) = a * count (hcube a b) := by
  show countF (hcubeF (hcube a b) a) = a * count (hcube a b)
  exact countF_hcubeF (hcube a b) a

/-! ## The dimension readout: `dim (hcube (a+1) b) = b` (the exponent) -/

/-- A nonempty axis of copies of `c` reads dimension `dim c` (every copy is
    the same cube, so the first one is representative). -/
theorem dimF_hcubeF_succ (c : HCube) (a : Nat) :
    dimF (hcubeF c (a + 1)) = dim c := rfl

/-- ★ **The dimension reads off the exponent**: the `b`-dimensional cube of
    side `a+1` has dimension `b`.  (Side `a+1`, not `a`, so the axes are
    nonempty and the depth is unambiguous — the `a=0` cube is degenerate.)
    Each rung adds exactly one axis (`dim_hcube_succ`). -/
theorem dim_hcube : ∀ (a b : Nat), dim (hcube (a + 1) b) = b
  | _, 0     => rfl
  | a, b + 1 => by
      show 1 + dimF (hcubeF (hcube (a + 1) b) (a + 1)) = b + 1
      rw [dimF_hcubeF_succ (hcube (a + 1) b) a, dim_hcube a b, Nat.add_comm]

/-- ★ **One dimension axis arises per rung (the DOF, read positively).**
    `dim (hcube (a+1) (b+1)) = dim (hcube (a+1) b) + 1` — climbing the count
    by one adjoins exactly one new axis (the dilation degree-of-freedom of L5,
    `DOF = rung − 2`), where the count pins each axis at the base. -/
theorem dim_hcube_succ (a b : Nat) :
    dim (hcube (a + 1) (b + 1)) = dim (hcube (a + 1) b) + 1 := by
  rw [dim_hcube a (b + 1), dim_hcube a b]

/-! ## The side readout: `side (hcube a (b+1)) = a` (the base) -/

/-- An axis of `a` copies has length `a`. -/
theorem lenF_hcubeF (c : HCube) : ∀ a, side.lenF (hcubeF c a) = a
  | 0     => rfl
  | a + 1 => by
      show 1 + side.lenF (hcubeF c a) = a + 1
      rw [lenF_hcubeF c a, Nat.add_comm]

/-- ★ **The side reads off the base**: a positive-dimensional cube of side `a`
    has `side = a` (the number of copies along its top axis). -/
theorem side_hcube (a b : Nat) : side (hcube a (b + 1)) = a := by
  show side.lenF (hcubeF (hcube a b) a) = a
  exact lenF_hcubeF (hcube a b) a

/-! ## ★★ The positive headline: `count = side ^ dim`, two different-typed readouts -/

/-- ★★★ **The `^`-object's positive law: cell-count = side raised to
    dimension.**  The one cube carries two *structurally distinct, different-
    typed* readouts — `side` (a **length**, the base `a+1`) and `dim` (a
    **dimension/axis count**, the exponent `b+1`) — and the cell count is the
    first raised to the second:

      `count (hcube (a+1) (b+1)) = side (…) ^ dim (…)`.

    This is `a^b` read **positively**: base = side (length), exponent =
    dimension (axis count), *different types* — which (`swap_changes_dim`) is
    why they do not swap.  The negative shadow ("`^` loses commutativity",
    `HyperAssoc.pow_not_comm`) is the count reading of this type-mismatch. -/
theorem count_eq_side_pow_dim (a b : Nat) :
    count (hcube (a + 1) (b + 1)) = side (hcube (a + 1) (b + 1)) ^ dim (hcube (a + 1) (b + 1)) := by
  rw [count_hcube, side_hcube, dim_hcube]

/-- **Swapping side and dimension changes the object's dimension.**  `hcube 2 3`
    is a 3-dimensional cube; `hcube 3 2` is a 2-dimensional cube — swapping the
    base and exponent swaps a *length* with a *dimension-count*, so the result
    lives in a different dimension (`3 ≠ 2`).  This is the structural,
    *positive* reason the count shadow reads `2^3 = 8 ≠ 9 = 3^2`
    (`HyperAssoc.pow_not_comm_concrete`): not "commutativity is lost" but
    "base and exponent are different types." -/
theorem swap_changes_dim : dim (hcube 2 3) ≠ dim (hcube 3 2) := by
  rw [show dim (hcube 2 3) = 3 from dim_hcube 1 3,
      show dim (hcube 3 2) = 2 from dim_hcube 2 2]
  decide

/-! ## Bridge: at dimension 2 the `^`-cube IS the `×`-square

`hcube a 2` is `a` copies of (`a` copies of a cell) — the same `a × a` block of
indistinguishable units that `UnitGrid.rows a a` lays out.  So the `^`-rung at
its first nontrivial dimension *is* the `×`-square: `a^2 = a · a` read on the
two objects.  (The two roads — operation-iteration here, the K_{3,2} grid in
`UnitGrid` — land on the same cell block; the no-exterior signature of the
frontier's "Why this matters".) -/

/-- **The dimension-2 cube is the `×`-square**: `count (hcube a 2) =
    UnitGrid.total (UnitGrid.rows a a)`, both `a^2 = a · a`.  `^` at dimension
    2 *is* `×` of the side with itself. -/
theorem count_hcube_two_eq_grid (a : Nat) :
    count (hcube a 2) = E213.Meta.Nat.UnitGrid.total (E213.Meta.Nat.UnitGrid.rows a a) := by
  rw [count_hcube, E213.Meta.Nat.UnitGrid.total_rows, Nat.pow_succ, Nat.pow_one]

end E213.Meta.Nat.UnitHyper
