/-!
# Minimal CW for the complex projective plane ℙ² — 213-native form

ℙ² (complex dim 2 = real dim 4) has minimal CW decomposition with
one cell in each even dimension:

  · 1 zero-cell `pt`            (point)
  · 1 two-cell `line`           (the hyperplane ℙ¹ ⊂ ℙ²)
  · 1 four-cell `plane`         (ℙ² itself, top cell)

(Odd dimensions are empty: H^1 = H^3 = 0.)

Cellular cohomology: H⁰ = H² = H⁴ = ℤ; all boundary maps are zero.

The cup ring is `ℤ[H] / (H³)` where `H ∈ H²` is the hyperplane
class.  The pivotal product is `H ⌣ H = [pt]`, giving the
**1×1 cup-pairing matrix `[1]` on H²** — signature (1, 0).

This is the simplest 4-fold example exhibiting **h^{2,0} = 0,
h^{1,1} = 1** Hodge structure: a clean contrast with T² (which
has h^{2,0} = 1, h^{1,1} = 1, signature (1, 1)).

Used by `HodgeConjecture/Pairing/HodgeIndexP2.lean` to lift
Hodge Index Theorem to the ℙ² instance — Picard rank ρ = 1
matches signature `(1, ρ − 1) = (1, 0)`.

STRICT ∅-AXIOM (all by `decide` / `rfl` on finite enumerations).
-/

namespace E213.Lib.Math.Cohomology.Surfaces.P2Minimal

/-- 0-cells: single point. -/
inductive Cell0 : Type
  | pt : Cell0
  deriving DecidableEq, Repr

/-- 2-cells: single 2-cell `line` representing the
    hyperplane class `H` ∈ H². -/
inductive Cell2 : Type
  | line : Cell2
  deriving DecidableEq, Repr

/-- 4-cells: single top cell `plane` representing the volume
    class (= [pt] under Poincaré duality). -/
inductive Cell4 : Type
  | plane : Cell4
  deriving DecidableEq, Repr

/-- ℤ-cochains at each non-trivial level (H¹ = H³ = 0 are not
    materialised). -/
abbrev C0 : Type := Cell0 → Int
abbrev C2 : Type := Cell2 → Int
abbrev C4 : Type := Cell4 → Int

/-- Cup-pairing `C² × C² → C⁴`.

    On the single basis class `H = line`, `H ⌣ H = [pt]` (= the
    `plane` generator).  In coefficient form this is just
    multiplication of the single C² coefficients. -/
def cup (α β : C2) : C4 :=
  fun _ => α Cell2.line * β Cell2.line

/-- The hyperplane class `H ∈ H²(ℙ²; ℤ)` — the single positive
    eigenclass of the cup-pairing. -/
def hyperplane_class : C2 := fun | Cell2.line => 1

/-- `H ⌣ H = +1` (the volume class).  Single positive eigenvalue
    ⟹ signature (1, 0). -/
theorem cup_HH : cup hyperplane_class hyperplane_class Cell4.plane = 1 := by decide

end E213.Lib.Math.Cohomology.Surfaces.P2Minimal
