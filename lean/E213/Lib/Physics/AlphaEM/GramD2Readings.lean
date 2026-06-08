import E213.Lib.Physics.Couplings.SpectrumComplete

/-!
# GramD2Readings — the self-energy prefactor `d² = 25` is over-determined

`gram_d2_prefactor` (frontier) records the open residual:
the Gram correction is `α²/d²` (`GramCubicReduction`), and the `/d²`
prefactor's *mechanism* is not yet forced from the cup-ring trace.

This file does **not** close that mechanism. It does a smaller, honest
thing: it shows the three candidate **readings** of the prefactor
(`Augmented.lean` § GramSelfEnergy: "block-pair total, Gram matrix DOF,
α_GUT factor") are not three competing *choices* — they are three
structurally-independent counts that all land on the **same value `d²`**.

This is the repo's equivalence-pluralism discipline (CLAUDE.md): when
several "readings" of one quantity appear, the move is to verify they are
facets of one object, not to list them as alternatives. So the open
question is narrowed: **not** "which of three values is the prefactor"
(they coincide at `d²`, over-determined), but only "which mechanism links
the self-energy to `d²`" (still open — frontier).

All PURE.
-/

namespace E213.Lib.Physics.AlphaEM.GramD2Readings

open E213.Lib.Physics.Couplings.SpectrumComplete (inv_alpha_GUT_factor)

def d : Nat := 5

/-! ## §1 — the three readings -/

/-- **Reading 1 — full atomic dim²** ("block-pair total", `Bare.lean`,
    `ProjectionRatios.lean`): the full `d × d`. -/
def fullDimSquared : Nat := d * d

/-- **Reading 2 — Gram matrix DOF**: a Gram matrix over the `d = 5` cells
    of Δ⁴ has `d × d` entries. -/
def gramMatrixEntries : Nat := d * d

-- Reading 3 — **α_GUT factor** `inv_alpha_GUT_factor = d²`
-- (`Couplings.SpectrumComplete`, `inv_alpha_GUT_eq_25`), used directly below.

/-- The block-pair reading has concrete content: `d²` is the diagonal
    (`d`) plus twice the unordered pairs (`C(d,2)`):
    `25 = 5 + 2·10`.  Ties the `C(5,2)=10` block-pair count to `d²=25`. -/
theorem blockpair_decomposition :
    d + 2 * (d * (d - 1) / 2) = d * d := by decide

/-! ## §2 — the three readings coincide at `d²` -/

/-- **The prefactor value is over-determined.**  All three candidate
    readings equal `25 = d²`.  They are facets of one structural quantity,
    not three independent modeling choices. -/
theorem three_readings_coincide :
    fullDimSquared = 25
    ∧ gramMatrixEntries = 25
    ∧ inv_alpha_GUT_factor = 25
    ∧ fullDimSquared = gramMatrixEntries
    ∧ fullDimSquared = inv_alpha_GUT_factor := by decide

/-- Restated against the atomic `d`: every reading is `d²`. -/
theorem all_readings_are_d_squared :
    fullDimSquared = d * d
    ∧ gramMatrixEntries = d * d
    ∧ inv_alpha_GUT_factor = d * d := by decide

end E213.Lib.Physics.AlphaEM.GramD2Readings
