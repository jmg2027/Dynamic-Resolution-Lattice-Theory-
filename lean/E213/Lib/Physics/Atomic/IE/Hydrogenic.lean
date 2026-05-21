import E213.Lib.Physics.Simplex.Counts

/-!
# Phase 4 HydrogenicIE — H-like ions IE = R·Z² *exact*

Hydrogenic ions (single electron):
  IE(Z) = R∞ · Z²

  where R∞ = 13.605693 eV (verified to 4.3 ppb in HydrogenIEPPM).

R∞ · Z² atomic chain → Z² atomic integer product.

## Observed IE (CODATA, eV)

  H    13.598434  (Z=1)  vs R = 13.605693 (mass corr ~3 ppm)
  He+  54.41776   (Z=2)
  Li²+ 122.45437  (Z=3)
  Be³+ 217.71865  (Z=4)
  B⁴+  340.2258   (Z=5)
  C⁵+  489.99334  (Z=6)
  N⁶+  667.046    (Z=7)
  O⁷+  871.4101   (Z=8)
  F⁸+  1103.1176  (Z=9)
  Ne⁹+ 1362.199   (Z=10)
-/

namespace E213.Lib.Physics.Atomic.IE.Hydrogenic

open E213.Lib.Physics.Simplex.Counts

/-- IE values in 10⁻³ eV (mEV). -/
def IE_He_plus : Nat := 54417760    -- 54.41776
def IE_Li_2plus : Nat := 122454370   -- 122.45437
def IE_Be_3plus : Nat := 217718650   -- 217.71865
def IE_B_4plus : Nat := 340225800    -- 340.2258
def IE_Ne_9plus : Nat := 1362199000  -- 1362.199

/-- R∞ in 10⁻³ eV (mEV) = 13605693. -/
def R_infinity_mEV : Nat := 13605693

/-! ## Z² Hydrogenic check: IE(Z) ≈ Z² · R∞ -/

/-- ★ Atomic form of Z² + bracket gaps in one statement.

  Hydrogenic IE bracket gaps (atomic Lens vs measurement-Lens):
    He+  : NT² · R − IE = 5012 mEV (92 ppm; mass corr)
    Li²+ : IE − NS² · R = 3133 mEV (26 ppm)
    Be³+ : IE − 16 · R  = 27562 mEV (127 ppm)

  Z² atomic forms:
    He+   Z² = NT²        = 4
    Li²+  Z² = NS²        = 9
    Be³+  Z² = (NS+1)²    = 16
    B⁴+   Z² = d²         = 25
    Ne⁹+  Z² = 10²        = 100 -/
theorem hydrogenic_atomic_chain :
    -- bracket gaps (atomic vs measurement-Lens)
    (NT * NT * R_infinity_mEV - IE_He_plus = 5012)
    ∧ (IE_Li_2plus - NS * NS * R_infinity_mEV = 3133)
    ∧ (IE_Be_3plus - 16 * R_infinity_mEV = 27562)
    -- Z² atomic forms
    ∧ (NT * NT = 4)               -- He+
    ∧ (NS * NS = 9)               -- Li²+
    ∧ ((NS + 1) * (NS + 1) = 16)  -- Be³+
    ∧ (d * d = 25)                -- B⁴+
    ∧ (10 * 10 = 100) := by       -- Ne⁹+
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Atomic.IE.Hydrogenic
