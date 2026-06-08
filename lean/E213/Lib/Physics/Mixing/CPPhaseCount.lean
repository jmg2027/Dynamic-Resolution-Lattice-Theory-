import E213.Lib.Physics.Simplex.Generations

/-!
# CPPhaseCount — 213 forces the EXISTENCE and UNIQUENESS of the CKM CP phase

The investigation of the apex phase `δ` established a sharp split: the apex
*modulus* `R_u = 1/φ²` is the real golden eigenvalue (derived), but the *phase*
`δ = π/φ²` is NOT an A₅ quantity (`Icosahedral.A5RealityNoCP`: A₅ is a real rep,
CP-conserving).  This file pins what **is** derived about the CP phase — not its
value, but its **existence and uniqueness** — from the derived generation count.

## Kobayashi–Maskawa counting from `N_gen = NS = 3`

For `N` generations, the CKM matrix `∈ U(N)` (`N²` real parameters) decomposes,
after removing the `2N−1` unphysical quark rephasings, into:

  · physical **mixing angles** `= N(N−1)/2`   (the real-orthogonal part);
  · physical **CP phases** `= (N−1)(N−2)/2`
        `= N(N+1)/2  −  (2N−1)`  (total phases minus rephasings).

`N_gen` is **derived** in DRLT: `N_gen = C(NS, NT) = C(3,2) = 3`
(`Generations.N_gen`, from `(3,2)` atomicity).  Substituting `N = NS = 3`:

  · angles `= 3·2/2 = 3`  (`θ₁₂, θ₁₃, θ₂₃` — Cabibbo + two);
  · **CP phases `= 2·1/2 = 1`** — exactly **one** physical CP phase `δ`.

So **CP violation existing, and being a single phase, is 213-forced** by the
derived `N_gen = 3`.  The falsifiable contrast:

  · `N = 2`:  `(2−1)(2−2)/2 = 0` phases — **no CP** (a 2-generation world is
    CP-conserving, the Cabibbo-only case);
  · `N = 4`:  `(4−1)(4−2)/2 = 3` phases.

`N_gen = 3` is the **minimal** generation count admitting CP violation — the
Kobayashi–Maskawa insight, here a *consequence* of `(NS,NT)=(3,2)` atomicity,
not an input.  (What remains open is the *value* of the one phase `δ`; the
A₅/golden route to it is closed — `A5RealityNoCP`.)

All theorems PURE.
-/

namespace E213.Lib.Physics.Mixing.CPPhaseCount

open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Lib.Physics.Simplex.Generations (N_gen)

/-- Physical CKM mixing angles for `N` generations: `N(N−1)/2`. -/
def ckmAngles (N : Nat) : Nat := N * (N - 1) / 2

/-- Physical CKM CP phases for `N` generations: `(N−1)(N−2)/2`. -/
def ckmPhases (N : Nat) : Nat := (N - 1) * (N - 2) / 2

/-! ## §1 — the counting, and `N_gen = 3 ⟹ 1 phase` -/

/-- ★★★ **KM counting closes: phases = total − rephasings.**  For `N`
    generations the physical CP phases `(N−1)(N−2)/2` equal the total phases
    `N(N+1)/2` minus the `2N−1` rephasings, at `N = 2,3,4`. -/
theorem km_counting_closes :
    ((2 - 1) * (2 - 2) / 2 = 2 * (2 + 1) / 2 - (2 * 2 - 1))      -- N=2: 0 = 3−3
    ∧ ((3 - 1) * (3 - 2) / 2 = 3 * (3 + 1) / 2 - (2 * 3 - 1))    -- N=3: 1 = 6−5
    ∧ ((4 - 1) * (4 - 2) / 2 = 4 * (4 + 1) / 2 - (2 * 4 - 1)) := by decide  -- N=4: 3 = 10−7

/-- ★★★★ **`N_gen = 3` forces exactly one CP phase (and three angles).**
    With the derived `N_gen = C(NS,NT) = 3`: `ckmAngles 3 = 3`, `ckmPhases 3 = 1`. -/
theorem three_generations_one_phase :
    N_gen = 3
    ∧ ckmAngles N_gen = 3
    ∧ ckmPhases N_gen = 1 := by decide

/-! ## §2 — falsifiable contrast: 2 generations ⇒ no CP -/

/-- ★★★ **CP needs ≥ 3 generations.**  `ckmPhases 2 = 0` (a 2-generation world
    is CP-conserving), `ckmPhases 3 = 1`, `ckmPhases 4 = 3`.  So `N_gen = 3` is
    the **minimal** count admitting CP violation — and DRLT derives `N_gen = 3`,
    so CP violation is forced to exist with exactly one phase. -/
theorem cp_needs_three_generations :
    ckmPhases 2 = 0 ∧ ckmPhases 3 = 1 ∧ ckmPhases 4 = 3
    -- 3 is minimal: phases jump 0 → 1 at N = 3
    ∧ ckmPhases 2 < ckmPhases 3 := by decide

/-! ## §3 — capstone -/

/-- ★★★★★ **213 forces the CP phase's existence + uniqueness.**  From the
    derived `N_gen = C(NS,NT) = 3`, Kobayashi–Maskawa counting gives exactly
    `(NS−1)(NS−2)/2 = 1` physical CP phase and `NS(NS−1)/2 = 3` mixing angles;
    `N = 2` would give `0` phases (no CP).  So CP violation existing, and being a
    *single* phase `δ`, is 213-derived (not posited) — only the *value* of `δ`
    is open (and not via A₅, which is CP-conserving). -/
theorem cp_phase_existence_unique :
    -- N_gen = 3 derived
    (N_gen = 3)
    -- exactly 1 CP phase, 3 angles
    ∧ ckmPhases N_gen = 1 ∧ ckmAngles N_gen = 3
    -- 2-gen contrast: 0 phases (no CP)
    ∧ ckmPhases 2 = 0
    -- the count is (NS−1)(NS−2)/2
    ∧ ckmPhases NS = (NS - 1) * (NS - 2) / 2 := by decide

end E213.Lib.Physics.Mixing.CPPhaseCount
