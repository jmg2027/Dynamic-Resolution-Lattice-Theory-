import E213.Meta.Nat.IntHelpers

/-!
# Minimal CW complex for the 2-torus T² — 213-native form

Standard topology: T² = ℝ²/ℤ² has minimal CW decomposition
  · 1 zero-cell `v`
  · 2 one-cells `a`, `b`  (the two non-trivial loops)
  · 1 two-cell `f`        (attached along a·b·a⁻¹·b⁻¹)

H⁰(T²; ℤ) = ℤ, H¹(T²; ℤ) = ℤ², H²(T²; ℤ) = ℤ.

In 213-native form: each k-cell type is a finite enumeration; the
ℤ-cochain at level k is the function space `Cell k → ℤ`.  All
boundary maps are zero (since the single 0-cell makes ∂a = v − v = 0,
and the 2-cell attaching word a·b·a⁻¹·b⁻¹ has zero boundary).

This makes T²'s cohomology ring directly enumerable: C⁰ ≅ ℤ,
C¹ ≅ ℤ², C² ≅ ℤ, with cohomology H^k = C^k.

Used by `HodgeConjecture/Pairing/HodgeIndexT2.lean` to lift the
ℤ/2-vacuous Hodge Index theorem to a non-vacuous form on a
213-canonical 2-fold.

STRICT ∅-AXIOM (all by `decide` / `rfl` on finite enumerations).
-/

namespace E213.Lib.Math.Cohomology.Surfaces.T2Minimal

/-- T²-minimal CW: 0-cells.  Single vertex `v`. -/
inductive Cell0 : Type
  | v : Cell0
  deriving DecidableEq, Repr

/-- T²-minimal CW: 1-cells.  Two non-trivial loops `a`, `b`. -/
inductive Cell1 : Type
  | a : Cell1
  | b : Cell1
  deriving DecidableEq, Repr

/-- T²-minimal CW: 2-cells.  Single face `f` (attached along
    a·b·a⁻¹·b⁻¹). -/
inductive Cell2 : Type
  | f : Cell2
  deriving DecidableEq, Repr

/-- ℤ-cochain at level 0 = `Cell0 → ℤ` ≅ ℤ. -/
abbrev C0 : Type := Cell0 → Int

/-- ℤ-cochain at level 1 = `Cell1 → ℤ` ≅ ℤ × ℤ. -/
abbrev C1 : Type := Cell1 → Int

/-- ℤ-cochain at level 2 = `Cell2 → ℤ` ≅ ℤ. -/
abbrev C2 : Type := Cell2 → Int

end E213.Lib.Math.Cohomology.Surfaces.T2Minimal
