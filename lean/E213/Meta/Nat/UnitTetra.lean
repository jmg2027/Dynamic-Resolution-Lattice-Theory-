import E213.Meta.Nat.UnitHyper
import E213.Meta.Nat.HyperLadder

/-!
# UnitTetra — the rung-4 object for `↑↑`: a cube whose dimension is a tower count

`UnitHyper` built the `^`-rung as the `b`-dimensional unit cube of side `a`
(`hcube a b`, `count = a^b`), the base setting the **side** and the exponent the
**dimension** — one dilation axis adjoined (`DOF = 1`).  Apply the layer rule
(`simplicial_operation_tower.md` L1) **once more**: tetration `↑↑` iterates `^`,
so its object is again a unit cube — but now the **dimension is itself a tower
count**, not a bare number.  That is the second dilation axis (`DOF = 2`).

  * `tetra a b` — the rung-4 cube: `cell` at `b = 0` (the point, `a↑↑0 = 1`);
    at `b+1`, the cube `hcube a (count (tetra a b))` — side `a`, **dimension =
    the previous rung-4 cell count** (`tetra_succ`).  Each rung feeds the whole
    previous tower as the next cube's dimension ("axis = previous layer", L1).
  * `count_tetra` — **`count (tetra a b) = hyperop 4 a b`**: the object *is*
    tetration (the `HyperLadder` rung 4), `a↑↑b = a^(a^(…^a))`.
  * `dof_four` — **`dofOfRung 4 = 2`**, derived by the `+1`-climb **twice** from
    the commutative `×`-base (`dof_two_comm`: DOF 0 → `^`: 1 → `↑↑`: 2): `↑↑`
    sits two dilation axes above `×`.
  * `hyperop_four_not_comm` — rung 4 does not commute (`2↑↑3 = 16 ≠ 27 = 3↑↑2`),
    a second non-commutative rung above `^`.

The DOF reading, positively: `^` lifts the count-clock to a **dimension** once
(base → dimension); `↑↑` lifts it **again** (the dimension is itself a `^`-count),
so the construction sits *two* count-lifts above the symmetric `×`-grid — `DOF =
rung − 2 = 2`.  The deeper "two distinguished axes" witness on the object (the
analogue of `UnitHyper.swap_changes_dim` for `^`) is left open (L5's 3- vs
4-simplex figure).

All ∅-axiom; reuses `UnitHyper.HCube`/`hcube`/`count`, the `HyperLadder` rung-4
recurrence, and the certified `DOF` base.
-/

namespace E213.Meta.Nat.UnitTetra

open E213.Meta.Nat.UnitHyper (HCube count hcube count_hcube)
open E213.Meta.Nat.HyperLadder
  (hyperop hyperop_climb hyperop_three dofOfRung dofOfRung_succ dof_two_comm)
open E213.Meta.Nat.HyperAssoc (Comm)

/-! ## The object: a cube whose dimension is the previous tower count -/

/-- The rung-4 (tetration) cube of side `a`.  Dimension `0` is a single cell
    (`a↑↑0 = 1`, the point); dimension `b+1` is the `^`-cube `hcube a (…)` whose
    **dimension is the cell count of the previous tetration cube** — the layer
    rule applied to `^` (the whole previous tower becomes the next dimension). -/
def tetra (a : Nat) : Nat → HCube
  | 0     => .cell
  | b + 1 => hcube a (count (tetra a b))

/-- The layer rule, named: rung 4 nests a `^`-cube whose dimension is the
    previous rung-4 count (`rfl`). -/
theorem tetra_succ (a b : Nat) :
    tetra a (b + 1) = hcube a (count (tetra a b)) := rfl

/-! ## The count readout: `count (tetra a b) = a ↑↑ b` (= `hyperop 4`) -/

/-- ★★★ **The object is tetration.**  `count (tetra a b) = hyperop 4 a b`
    (`= a↑↑b`): the rung-4 cube's cell count is the rung-4 operation of the
    ladder.  At `b+1` the cube has side `a` and dimension `count (tetra a b)`, so
    its count is `a ^ (count (tetra a b))` (`count_hcube`); the ladder's climb
    (`hyperop_climb` + `hyperop_three`) reads the same `a ^ (hyperop 4 a b)`. -/
theorem count_tetra (a : Nat) : ∀ b, count (tetra a b) = hyperop 4 a b
  | 0     => rfl
  | b + 1 => by
      show count (hcube a (count (tetra a b))) = hyperop 4 a (b + 1)
      rw [count_hcube, count_tetra a b, hyperop_climb 3 a b, hyperop_three]

/-! ## The DOF certification: `dofOfRung 4 = 2`, two lifts above the `×`-base -/

/-- ★★ **`DOF = 2` at rung 4**, derived (not asserted) by the `+1`-per-rung climb
    **twice** from the commutative `×`-base: `×` carries DOF 0 (`dof_two_comm`,
    the grid transpose), `^` adds one dilation axis (DOF 1), `↑↑` adds a second
    (DOF 2).  So tetration sits two dilation degrees-of-freedom above the
    symmetric `×`-grid — the object `tetra` lifts the count-clock to a dimension
    twice (the dimension is itself a tower count, `count_tetra`). -/
theorem dof_four : dofOfRung 4 = 2 :=
  calc dofOfRung 4 = dofOfRung 3 + 1 := dofOfRung_succ 3 (by decide)
    _ = (dofOfRung 2 + 1) + 1 := by rw [dofOfRung_succ 2 (by decide)]
    _ = 2 := by rw [dof_two_comm.1]

/-- Rung 4 (`↑↑`) does **not** commute: `2↑↑3 = 2^(2^2) = 16 ≠ 27 = 3^3 = 3↑↑2`.
    A second non-commutative rung above `^` — the operands stay different types
    as the tower climbs. -/
theorem hyperop_four_not_comm : ¬ Comm (hyperop 4) := by
  intro h
  exact absurd (h 2 3) (by decide)

end E213.Meta.Nat.UnitTetra
