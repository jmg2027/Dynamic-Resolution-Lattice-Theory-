import E213.Meta.Nat.PureNat

/-!
# Shape213 — the internal readout is the shape (a factorization)

`GridReadout213` proposed `perimeter = 2 * (a + b)` as a *second*,
independent source of vector-valued readout — the boundary of the grid.
That `perimeter` is an **imported Euclidean readout**: an abstract
unit-grid of indistinguishable cells has no boundary, no embedding, no
metric — "perimeter" only exists once the cells are placed in the plane.
The import is the illusion of a *second independent source*.

The honest internal readout is the **shape** = an ordered factorization,
the list of side-counts.  Everything reads off the factorization alone:

* `shapeProduct` — the **area** readout is the **product-collapse** of the
  shape (`[] => 1`, `a :: l => a * shapeProduct l`);
* `dimension` — the **substrate dimension** is the **number of factors**
  = the bare-recursion length of the shape;
* `dim_one_is_count` — a 1-D shape `[n]` (a line) reads off the bare
  count `n`: the single readout of the 1-D substrate;
* `shape_splits` — the import-free replacement for
  `GridReadout213.readout_splits`: two **distinct shapes** with **equal
  area** (`[1,6] ≠ [2,3]`, both product `6`), the shape itself being the
  second readout, **no perimeter needed**;
* `refine_preserves_product` — splitting one factor (`a*b :: l` into
  `a :: b :: l`) preserves the area: the product-collapse is
  **dimension-invariant**;
* `refine_increases_dimension` — splitting one factor adds exactly one
  dimension.  Together with the previous: `dimension` is the **free axis**
  along the factorization, `shapeProduct` the **dimension-invariant
  collapse** — not two independent readouts but one structure, the
  factorization, read at two angles.

So a `d`-dimensional grid is a `d`-factor factorization, and the **prime
(atom) factorization is the maximal-dimension shape**: refining stops only
when no factor splits nontrivially = every factor is an atom (prime).  The
atom-shape grouped by value is exactly `exp`, the ×-count-Lens
(`E213.Meta.Nat.VpMul.vp_mul`).  Hence **substrate dimension** and
**atom-coloring (`exp`)** are ONE structure — the ×-atom / factorization —
at different resolutions, NOT two independent sources of vector-valued
readout.  `refine_chain` gives the concrete depth-1 → depth-2 witness:
`6` refining into its atoms `2, 3`, product fixed, dimension +1.

All ∅-axiom: bare recursion + bare induction, `decide`/`rfl` on closed
concrete `Nat`/`List`, no core `List` lemmas (which carry `propext`).
-/

namespace E213.Meta.Nat.Shape213

/-! ### The shape, its product-collapse, and its dimension -/

/-- The **area** readout: the product-collapse of the shape (the list of
    side-counts).  Bare recursion — `[] => 1`, `a :: l => a * (…)` — so it
    never touches core `List.prod` (which carries `propext`). -/
def shapeProduct : List Nat → Nat
  | []     => 1
  | a :: l => a * shapeProduct l

/-- The **substrate dimension**: the number of factors in the shape =
    its bare-recursion length.  `[] => 0`, `_ :: l => dimension l + 1` —
    no core `List.length`. -/
def dimension : List Nat → Nat
  | []     => 0
  | _ :: l => dimension l + 1

/-! ### ★ The 1-D substrate: a single count readout -/

/-- ★ **A 1-D shape reads off the bare count.**  A length-1 shape `[n]`
    (a line) has area `n`: the single readout of the 1-D substrate, the
    line of `n` units.  (`shapeProduct [n] = n * 1 = n`.) -/
theorem dim_one_is_count (n : Nat) : shapeProduct [n] = n := by
  show n * shapeProduct ([] : List Nat) = n
  show n * 1 = n
  rw [Nat.mul_one]

/-! ### ★★ The split: the shape is the second readout, internal -/

/-- ★★ **The shape does not collapse to the area** — the import-free
    replacement for `GridReadout213.readout_splits`.  Two **distinct
    shapes** carry **equal area** with **no perimeter / no Euclidean
    embedding** invoked: `[1,6] ≠ [2,3]` yet `shapeProduct [1,6] = 6 =
    shapeProduct [2,3]`.  The shape itself is the second readout, and it
    is internal — a factorization, not a boundary. -/
theorem shape_splits :
    ([1, 6] ≠ [2, 3]) ∧ (shapeProduct [1, 6] = shapeProduct [2, 3]) := by
  apply And.intro
  · decide
  · decide

/-! ### ★ Refinement: split a factor, fix the area, add a dimension -/

/-- ★ **Refining a factor preserves the area.**  Splitting one factor —
    `a*b :: l` becoming `a :: b :: l` — leaves the product-collapse
    unchanged: the area is **dimension-invariant**, the product just
    re-associates (`PureNat.mul_assoc`).  Moving along the factorization
    without changing the count. -/
theorem refine_preserves_product (a b : Nat) (l : List Nat) :
    shapeProduct (a * b :: l) = shapeProduct (a :: b :: l) := by
  show a * b * shapeProduct l = a * (b * shapeProduct l)
  exact PureNat.mul_assoc a b (shapeProduct l)

/-- ★ **Refining a factor adds exactly one dimension.**  Splitting
    `a*b :: l` into `a :: b :: l` raises the factor count by one:
    `dimension (a :: b :: l) = dimension (a*b :: l) + 1`.  So `dimension`
    is the **free axis** along the factorization, while `shapeProduct`
    (above) is the **dimension-invariant collapse**. -/
theorem refine_increases_dimension (a b : Nat) (l : List Nat) :
    dimension (a :: b :: l) = dimension (a * b :: l) + 1 := by
  show (dimension l + 1) + 1 = (dimension l + 1) + 1
  rfl

/-! ### ★ The maximal refinement: the prime (atom) shape = `exp`

Refinement (`refine_*`) splits factors, raising the dimension and fixing
the area, until no factor splits nontrivially — i.e. every factor is an
**atom (prime)**.  That maximal-dimension shape, grouped by value, is the
prime factorization = `exp`, the ×-count-Lens
(`E213.Meta.Nat.VpMul.vp_mul`).  So the substrate dimension and the
atom-coloring are ONE structure at different resolutions, not two
independent sources of vector-valued readout.

`refine_chain` instantiates `refine_preserves_product` +
`refine_increases_dimension` on the concrete atomic split `6 = 2 * 3`:
the depth-1 shape `[6]` refines to the depth-2 atom-shape `[2,3]`, area
fixed at `6`, dimension `1 → 2`.  `[2,3]` is maximal: `2` and `3` are
atoms, no further nontrivial split. -/

/-- ★ **The depth-1 → depth-2 atom refinement of `6`.**  Concrete witness
    of the refinement chain reaching the atom-shape: `[6]` refines to its
    prime factorization `[2, 3]`, the **product is preserved**
    (`shapeProduct [6] = 6 = shapeProduct [2,3]`) and the **dimension goes
    up by one** (`dimension [2,3] = 2 = dimension [6] + 1`).  The
    maximal-dimension shape of `6` is its atom-shape — this is the
    elementary instance of "the prime factorization is the
    maximal-dimension factorization", i.e. `exp`. -/
theorem refine_chain :
    (shapeProduct [6] = shapeProduct [2, 3]) ∧
    (dimension [2, 3] = dimension [6] + 1) := by
  apply And.intro
  · -- `shapeProduct [2,3] = shapeProduct (2*3 :: []) = shapeProduct [6]`
    show shapeProduct [6] = shapeProduct (2 * 3 :: ([] : List Nat))
    rw [refine_preserves_product 2 3 []]
  · -- `dimension [2,3] = dimension (2*3 :: []) + 1 = dimension [6] + 1`
    exact refine_increases_dimension 2 3 []

end E213.Meta.Nat.Shape213
