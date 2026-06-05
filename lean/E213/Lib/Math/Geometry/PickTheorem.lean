import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

/-!
# Pick's theorem — the lattice-count ↔ area bridge (∅-axiom, rectangle atom)

Pick (1899): the area of a simple lattice polygon is `A = I + B/2 − 1`, where `I`
counts interior lattice points and `B` counts boundary lattice points.  This is a
cross-domain gem — a **discrete count** (`I`, `B`, number theory / combinatorics)
equals a **continuous area** (`A`, geometry).  In proof-ISA terms it is a
*two-readings-agree* identity: the count-fold and the area-fold of one figure
coincide (the GRA-universality shape, at lattice scale).

Stated with the denominator cleared (`pickValue = 2·A`), so everything is integer:

  `2·I + B − 2 = 2·A`.

This file closes the **rectangle atom** — the base case from which the general
theorem is assembled by additivity — as a pure `ℤ` ring identity (`ring_intZ`).
The triangle case and additive assembly to general polygons (needing the diagonal
boundary count `= gcd(w,h) − 1`) are the open rungs:
`research-notes/frontiers/pick_theorem/`.

## Rectangle counts (axis-aligned `[0,w] × [0,h]`, `w,h ≥ 1`)

- interior points  `I = (w−1)(h−1)`,
- boundary points  `B = 2w + 2h`,
- twice the area    `2A = 2wh`.
-/

namespace E213.Lib.Math.Geometry.PickTheorem

open E213.Meta.Int213

/-- Pick's functional with the denominator cleared: `2·A = 2·I + B − 2`. -/
def pickValue (I B : Int) : Int := 2 * I + B - 2

/-- **Pick's relation for a rectangle** — NOT Pick's theorem.  This is a one-line
    `ring_intZ` cancellation: *given* the (separately known) point counts of a
    lattice rectangle `I = (w−1)(h−1)`, `B = 2w + 2h`, the linear combination
    `2I + B − 2` equals `2wh`.  The content of Pick's theorem proper — that
    `I + B/2 − 1` equals the area for an *arbitrary* simple lattice polygon, via
    triangulation + the elementary-triangle base case + the diagonal count
    `gcd(w,h)−1` — is the open frontier (`research-notes/frontiers/pick_theorem/`),
    not this. -/
theorem pick_rectangle (w h : Int) :
    pickValue ((w - 1) * (h - 1)) (2 * w + 2 * h) = 2 * (w * h) := by
  unfold pickValue
  ring_intZ

/-- Unit square `[0,1]²`: `I = 0`, `B = 4`, area `1` — `2·0 + 4 − 2 = 2 = 2·1`. -/
theorem pick_unit_square : pickValue 0 4 = 2 * 1 := by decide

/-- `2×3` rectangle: `I = (1)(2) = 2`, `B = 10`, area `6` — `4 + 10 − 2 = 12`. -/
theorem pick_2x3 : pickValue ((2 - 1) * (3 - 1)) (2 * 2 + 2 * 3) = 2 * (2 * 3) := by
  decide

end E213.Lib.Math.Geometry.PickTheorem
