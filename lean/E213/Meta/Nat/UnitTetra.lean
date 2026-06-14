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

open E213.Meta.Nat.UnitHyper (HCube count hcube count_hcube dim dim_hcube side side_hcube)
open E213.Meta.Nat.HyperLadder
  (hyperop hyperop_climb hyperop_three dofOfRung dofOfRung_succ dof_two_comm)
open E213.Meta.Nat.HyperAssoc (Comm)
open E213.Meta.Nat.PowBasic (one_le_pow)

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

/-! ## §2 — the two distinguished axes (the direct DOF-2 witness on the object)

The rung-3 witness `UnitHyper.swap_changes_dim` showed `^` carries **one**
distinguished axis: the dimension reads the exponent (an axis count) while the
side reads the base (a length) — different types.  On `tetra` the same two
readouts persist, but the **dimension axis is itself lifted one level higher**,
giving the second degree-of-freedom:

  * `side (tetra (a+1) (b+1)) = a+1` — the **side** still reads the base, a
    **length** (`side_tetra_succ`);
  * `dim (tetra (a+1) (b+1)) = count (tetra (a+1) b)` — the **dimension** is no
    longer a *bare height* `b+1` (as it is at `^`, `UnitHyper.dim_hcube`); it is
    **itself a tower cell count** (`dim_tetra_succ`).

So where `^` reads `count = side ^ (bare height)` (`UnitHyper.count_eq_side_pow_dim`,
dimension = a plain operand), `↑↑` reads `count = side ^ (a tower count)`
(`count_tetra_pow`): the dimension-clock is lifted a **second** time.  The two
axes — the length `side` and the *itself-lifted* dimension — are the `DOF = 2`,
read directly off the object (the rung-4 analogue of the rung-3 `swap_changes_dim`,
now a *level* difference in the dimension axis rather than a single swap). -/

/-- The rung-4 cube has a positive cell count (side `a+1 ≥ 1`): `1 ≤ count
    (tetra (a+1) b)`.  Needed to read the side off the dimension-`≥1` cube. -/
theorem count_tetra_pos (a : Nat) : ∀ b, 1 ≤ count (tetra (a + 1) b)
  | 0     => Nat.le_refl 1
  | b + 1 => by
      show 1 ≤ count (hcube (a + 1) (count (tetra (a + 1) b)))
      rw [count_hcube]
      exact one_le_pow (Nat.succ_le_succ (Nat.zero_le a)) _

/-- ★ **The second axis: the dimension is itself a tower count.**  Where `^`'s
    dimension is a bare height (`UnitHyper.dim_hcube : dim (hcube (a+1) (b+1)) =
    b+1`, a plain operand), `↑↑`'s dimension is the **cell count of the previous
    rung-4 cube**: `dim (tetra (a+1) (b+1)) = count (tetra (a+1) b)`.  The
    dimension-clock is lifted a second time — the `DOF 1 → 2` step. -/
theorem dim_tetra_succ (a b : Nat) :
    dim (tetra (a + 1) (b + 1)) = count (tetra (a + 1) b) := by
  show dim (hcube (a + 1) (count (tetra (a + 1) b))) = count (tetra (a + 1) b)
  exact dim_hcube a (count (tetra (a + 1) b))

/-- ★ **The first axis: the side reads the base (a length).**  `side (tetra
    (a+1) (b+1)) = a+1` — the same length readout as `^` (`UnitHyper.side_hcube`),
    inherited unchanged. -/
theorem side_tetra_succ (a b : Nat) : side (tetra (a + 1) (b + 1)) = a + 1 := by
  obtain ⟨D, hD⟩ : ∃ D, count (tetra (a + 1) b) = D + 1 :=
    ⟨count (tetra (a + 1) b) - 1,
      (Nat.succ_pred_eq_of_pos (count_tetra_pos a b)).symm⟩
  show side (hcube (a + 1) (count (tetra (a + 1) b))) = a + 1
  rw [hD]
  exact side_hcube (a + 1) D

/-- ★★ **`count = side ^ (a tower count)`** — the DOF-2 reading.  The cell count
    of the rung-4 cube is the side raised to a dimension that is *itself* a tower
    count: `count (tetra (a+1) (b+1)) = (a+1) ^ count (tetra (a+1) b)`.  Contrast
    `^`'s `count = side ^ (bare height)`: the exponent here is a full tower, the
    second lift. -/
theorem count_tetra_pow (a b : Nat) :
    count (tetra (a + 1) (b + 1)) = (a + 1) ^ count (tetra (a + 1) b) := by
  show count (hcube (a + 1) (count (tetra (a + 1) b))) = (a + 1) ^ count (tetra (a + 1) b)
  exact count_hcube (a + 1) (count (tetra (a + 1) b))

end E213.Meta.Nat.UnitTetra
