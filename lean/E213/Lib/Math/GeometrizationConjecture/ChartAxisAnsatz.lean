import E213.Lens.LensCore
import E213.Meta.LensInternality

/-!
# G121 — Chart-axis ansatz (open conjecture, definitional form)

Records the G121 §4.1 ansatz as a parametric Lean definition.

**This file is NOT a structural derivation.**  Per
`research-notes/G121_dim4_self_pointing_axis.md` §6.2 (knot M2),
the structural justification — *why* one of the d_213 axes is
chart-invisible per `seed/AXIOM/07_self_reference.md` §8.1 — is
open.  This file encodes the ansatz as a *definition* in Lean so
that future work (R1 in G121 §7) can derive it, falsify it, or
specialise it to other K_{NS, NT}^{(c)} deployments.

## What is encoded

  · `chartBase NS NT := NS + NT`
      — fractal base from K_{NS,NT}^{(c)} bipartite axis total.
        For K_{3,2}^{(c=2)} agrees with G44 `substrate_sum`
        (`Lib/Math/BipartiteDecomp/G44Capstone.lean`, value 5).
  · `selfPointingAxes : Nat := 1`
      — count of axes structurally absent from chart-Lens readout
        per the G121 ansatz §4.1.  Derivation: open (M2).
  · `chartVisibleAxes NS NT := chartBase NS NT - selfPointingAxes`
      — externally-visible chart-Lens axis count under the ansatz.

## What this file is NOT

  · Not a derivation of `selfPointingAxes = 1`.  That is the open
    knot M2 (G121 §6.2).
  · Not a derivation of `chartBase NS NT = NS + NT` from
    K_{NS, NT}^{(c)} structural axioms — it is a definitional
    encoding consistent with G44 substrate sum (numerical match).
  · Not a universe-constant claim.  `chartBase` is parametric in
    (NS, NT); the K_{3,2} value 5 is one specialisation, not a
    privileged constant (per G120 §11 audit framing discipline).
  · Not a precision result.  No ppb/ppm numerical prediction.

## Specialisation predictions

| Deployment | chartBase | chartVisibleAxes |
|---|---|---|
| K_{3,2}^{(c=2)} | 5 | 4 ← spacetime |
| K_{2,2} | 4 | 3 |
| K_{4,2} | 6 | 5 |
| K_{3,3} | 6 | 5 |

If a 213-consistent deployment with `chartVisibleAxes ≠ 4`
turns out to be valid physics, the K_{3,2} anchoring of G121
is falsified.  No such alternative deployment is currently
established.

∅-axiom: every theorem is rfl over Nat arithmetic.  No imports
beyond Lean 4 core.  No Mathlib / Classical / propext /
Quot.sound / native_decide.

Cross-reference: `research-notes/G121_dim4_self_pointing_axis.md`
for the full narrative + 4 open knots (M1-M4).
-/

namespace E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz

open E213.Lens (Lens)

/-- Fractal base of the K_{NS, NT}^{(c)} deployment.

    Defined as `NS + NT` per G44 substrate sum.  For K_{3,2}^{(c=2)}
    this equals 5; parametric form here.  Not claimed as a universe
    constant.
-/
def chartBase (NS NT : Nat) : Nat := NS + NT

/-- Count of chart-Lens-invisible axes under the G121 ansatz §4.1.

    Per `seed/AXIOM/07_self_reference.md` §8.1 (no exterior), the
    self-pointing residue does not pass through chart-Lens readout.
    The ansatz commits to exactly **one** such axis.

    Structural derivation: open (G121 §6.2, knot M2).  A future
    Lens-level theorem in `lean/E213/Lens/` may derive this from
    chart-Lens + self-reference axioms; until then, the `1` is the
    ansatz committed to.
-/
def selfPointingAxes : Nat := 1

/-- Chart-Lens visible axis count under G121 ansatz.

    External observer counts `chartBase - selfPointingAxes` axes.
    For K_{3,2}^{(c=2)} this is 4 (the conjectured spacetime
    dimension d_M).
-/
def chartVisibleAxes (NS NT : Nat) : Nat :=
  chartBase NS NT - selfPointingAxes

/-! ## Arithmetic identities -/

/-- Unfold form: `chartVisibleAxes = chartBase - 1`. -/
theorem chartVisibleAxes_eq_base_minus_one (NS NT : Nat) :
    chartVisibleAxes NS NT = chartBase NS NT - 1 := rfl

/-- Direct unfold to `NS + NT - 1`. -/
theorem chartVisibleAxes_unfold (NS NT : Nat) :
    chartVisibleAxes NS NT = NS + NT - 1 := rfl

/-! ## K_{3,2}^{(c=2)} specialisation — main empirical anchor -/

/-- `chartBase 3 2 = 5` — agrees with G44 `substrate_sum`. -/
theorem chartBase_K32 : chartBase 3 2 = 5 := rfl

/-- `chartVisibleAxes 3 2 = 4` — the conjectured d_M for the
    K_{3,2}^{(c=2)} deployment, matching the standard-math
    critical exotic-residue dimension (Freedman + Donaldson). -/
theorem chartVisibleAxes_K32 : chartVisibleAxes 3 2 = 4 := rfl

/-- Spacetime 3+1 partition (G121 §4.2):
    chartVisibleAxes splits as N_S + (N_T - 1) — N_S axes for
    space readout, one N_T axis for time readout, the other
    N_T axis absorbed into self-pointing. -/
theorem spacetime_partition_K32 :
    chartVisibleAxes 3 2 = 3 + (2 - 1) := rfl

/-! ## Alternative-deployment predictions (falsifier candidates) -/

/-- K_{2,2}: `chartVisibleAxes = 3`. -/
theorem chartVisibleAxes_K22 : chartVisibleAxes 2 2 = 3 := rfl

/-- K_{4,2}: `chartVisibleAxes = 5`.  Would predict critical
    exotic-residue at d_M = 5; contradicts Kervaire-Milnor finite
    Θ_d at d ≥ 5.  Hence K_{4,2}-deployment of 213 (if any) would
    falsify G121 §4.1 ansatz. -/
theorem chartVisibleAxes_K42 : chartVisibleAxes 4 2 = 5 := rfl

/-- K_{3,3}: `chartVisibleAxes = 5`. -/
theorem chartVisibleAxes_K33 : chartVisibleAxes 3 3 = 5 := rfl

/-! ## Bundle -/

/-- The K_{3,2}^{(c=2)} ansatz bundle — four arithmetic facts that
    the G121 ansatz §4.1 commits to.  Future Lens-level work
    (R1, M2-close) must derive `selfPointingAxes = 1` from
    chart-Lens + self-reference axioms to upgrade this from
    definitional encoding to structural theorem. -/
theorem K32_ansatz_bundle :
    chartBase 3 2 = 5
    ∧ chartVisibleAxes 3 2 = 4
    ∧ chartVisibleAxes 3 2 = 3 + (2 - 1)
    ∧ selfPointingAxes = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Axiom-level shadow (R1 partial close — 2026-05-22)

The deployment-level ansatz `selfPointingAxes := 1` matches an
**axiom-level fact derivable from `Meta/LensInternality`**:

  `Lens α ≃ α × α × (α → α → α)`

i.e. every Lens carries exactly 3 data components — `base_a`,
`base_b` (atom-data, 2 components) and `combine` (operator-data,
1 component).  The split `3 = 2 + 1` is the axiom-level shadow of
the deployment-level `chartVisibleAxes = chartBase - 1`.

Per `Meta/LensInternality.lens_is_raw_internal` (§8.1
formalisation): every Lens is Raw-internal, with data exactly the
`(base_a, base_b, combine)` triple.  Of these three components,
two correspond to Clause-1 atoms (chart-readable as α-values) and
one corresponds to Clause-2 slash-operator (the *combine* function,
which is the self-encoding of how Lens itself processes Raw).

The axiom-level shadow does **not** structurally derive the
deployment-level claim: the deployment-level chart-Lens (over
K_{NS, NT}^{(c)} hinge) is not the same object as the Raw-level
Lens type.  Linking them is the real M2 close (R1 in G121 §7).
This section records the *consistency check*: deployment-level
`selfPointingAxes := 1` is consistent with the axiom-level
self-pointing component count of `1` (the combine).
-/

/-- Count of atom-data components in every Lens (per
    `Meta/LensInternality`: `base_a` + `base_b`). -/
def axiomAtomComponents : Nat := 2

/-- Count of operator-data components in every Lens (per
    `Meta/LensInternality`: `combine`).  This is the axiom-level
    shadow of `selfPointingAxes`. -/
def axiomOperatorComponents : Nat := 1

/-- Total Lens data components per `Meta/LensInternality.lens_is_raw_internal`:
    `Lens α ≃ α × α × (α → α → α)` has exactly 3 components. -/
def axiomLensDataTotal : Nat :=
  axiomAtomComponents + axiomOperatorComponents

/-- Axiom-level total component count = 3. -/
theorem axiomLensDataTotal_eq_three : axiomLensDataTotal = 3 := rfl

/-- Axiom-level shadow: `total - operator = atom`, matching the
    deployment-level pattern `chartBase - selfPointingAxes
    = chartVisibleAxes`. -/
theorem axiom_shadow_split :
    axiomLensDataTotal - axiomOperatorComponents = axiomAtomComponents := rfl

/-- Axiom-level shadow consistency with deployment-level ansatz:
    the operator-component count at axiom-level matches the
    `selfPointingAxes` commitment at deployment-level. -/
theorem axiom_shadow_consistency :
    axiomOperatorComponents = selfPointingAxes := rfl

/-- Axiom-level shadow bundle: 3-component Lens data with 2-atom +
    1-operator split, consistent with G121 ansatz §4.1. -/
theorem axiom_level_shadow_bundle :
    axiomLensDataTotal = 3
    ∧ axiomLensDataTotal - axiomOperatorComponents = axiomAtomComponents
    ∧ axiomOperatorComponents = selfPointingAxes
    ∧ axiomAtomComponents = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Direct invocation of `Lens` 3-tuple decomposition

The shadow encoding above (`axiomAtomComponents`,
`axiomOperatorComponents`) is consistent with the Lean-level
`Lens` structure (`Lens/LensCore.lean:34-37`):

```
structure Lens (α : Type) where
  base_a  : α          -- atom-data, Clause 1 first atom
  base_b  : α          -- atom-data, Clause 1 second atom
  combine : α → α → α  -- operator-data, Clause 2 slash
```

Exactly 3 fields.  The theorems below invoke `Lens α` directly
and witness the 3-tuple decomposition via `Meta.LensInternality.toData`.
-/

/-- Witness: every `Lens α`'s `toData` projects to the 3-tuple
    `(base_a, base_b, combine)`.  This is the Lean-level
    counterpart of `axiomLensDataTotal = 3`. -/
theorem lens_toData_three_tuple (α : Type) (L : Lens α) :
    (E213.Meta.LensInternality.toData L).1 = L.base_a
    ∧ (E213.Meta.LensInternality.toData L).2.1 = L.base_b
    ∧ (E213.Meta.LensInternality.toData L).2.2 = L.combine :=
  ⟨rfl, rfl, rfl⟩

/-- Witness: the 3-tuple decomposes as atom-data (2 components)
    followed by operator-data (1 component).  The split position
    matches `axiomAtomComponents + axiomOperatorComponents`. -/
theorem lens_toData_split (α : Type) (L : Lens α) :
    let d := E213.Meta.LensInternality.toData L
    (d.1, d.2.1) = (L.base_a, L.base_b)
    ∧ d.2.2 = L.combine :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz
