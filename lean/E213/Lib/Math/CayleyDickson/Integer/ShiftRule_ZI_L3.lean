import E213.Lib.Math.CayleyDickson.Integer.ZI
import E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2Tower

/-!
# SHIFT RULE — smallest instance: ZI units ≅ ZSqrt[-2] L3T units

Discovered by Rust probe (2026-05-09): D ≥ 2 ladders are shifted-by-one
copies of D=1 ladder.  Smallest non-trivial instance: ZI itself
(D=1 L2, 4 units = Z_4) is unit-loop-isomorphic to L3T (D=2 L3, 4 units).

This file pins that isomorphism as ∅-axiom decidable Lean theorem.

213-native: no external "Z_4" name imported.  The statement is purely
"explicit bijection between two 213 corpus objects preserves multiplication".
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

open E213.Lib.Math.CayleyDickson.Integer.ZI

def ZIUnits : List ZI := [⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]

def L3TUnits : List L3T :=
  [⟨⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩,
   ⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-1, 0⟩⟩]

/-- Explicit bijection ZI → L3T (real-slot to real-slot). -/
def φ : ZI → L3T
  | ⟨1, 0⟩    => ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
  | ⟨-1, 0⟩   => ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩
  | ⟨0, 1⟩    => ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
  | ⟨0, -1⟩   => ⟨⟨0, 0⟩, ⟨-1, 0⟩⟩
  | _         => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩  -- catchall (not in unit set)

/-- ★ ∅-axiom shift-rule witness: φ preserves multiplication on all
    16 unit-pair products, by direct decidable computation. -/
theorem shift_iso_L3 :
    ∀ a ∈ ZIUnits, ∀ b ∈ ZIUnits, φ (ZI.mul a b) = φ a * φ b := by decide

/-- Bijectivity check (4 distinct image elements). -/
theorem φ_injective_on_units :
    (ZIUnits.map φ).length = ZIUnits.length ∧
    (ZIUnits.map φ).Nodup := by decide

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
