/-!
# Neutrino zero-dial mass floor — the over-determination arithmetic (∅-axiom)

The DRLT reading fixes one number, `r = m₃/m₂ = 5.71` (docstring level,
`Foundations/DrltZeroParameters`; provenance repair is an open item — see
`research-notes/frontiers/neutrino_mass_floor_falsifier.md`, active scratch).
The measured splitting ratio fixes a second.  Together they over-determine
the lightest mass with **zero dials**:

    ρ = Δm²₃₁/Δm²₂₁ = (r² − x)/(1 − x),   x := (m₁/m₂)²
    ⟹  x = (ρ − r²)/(ρ − 1),   and the reading REQUIRES x ≥ 0, i.e. ρ ≥ r².

Every theorem below is pure ℕ arithmetic (cross-multiplied rational
inequalities); the measured values enter as *quoted integers* in units of
`10⁻⁷ eV²` (global-fit central values, normal ordering, quoted 2026):

    dm21 = 741   (Δm²₂₁ = 7.41×10⁻⁵ eV²)
    dm31 = 25110 (Δm²₃₁ = 2.511×10⁻³ eV²)
    r    = 571/100,  r² = 326041/10⁴

The theorems are the *conditional* falsifier core (the typed-hypothesis
pattern): IF the measured central values are as quoted, THEN the reading
survives with `x ∈ [0.038, 0.039]` — hence `m₁/m₂ ≈ 0.197`, and (docstring
arithmetic) `m₂ ≈ 8.8 meV`, `m₃ ≈ 50 meV`, `Σm_ν ≈ 61 meV`.  The kill line
is sharp: a solar splitting at or above `7.71×10⁻⁵ eV²` (same `Δm²₃₁`)
falsifies the ratio reading outright — `kill_line_at_771`.  JUNO's
sub-percent solar measurement decides.  Catalog: `catalogs/falsifiers.md` F3.
-/

namespace E213.Lib.Physics.Mixing.NeutrinoMassFloor

/-- Measured solar splitting, units 10⁻⁷ eV² (quoted input). -/
def dm21 : Nat := 741

/-- Measured atmospheric splitting, units 10⁻⁷ eV² (quoted input). -/
def dm31 : Nat := 25110

/-- Numerator of r² for r = 571/100 (r² = 326041/10⁴). -/
def rSqNum : Nat := 326041

/-- Denominator of r². -/
def rSqDen : Nat := 10000

/-- ★ **Survival inequality** — `ρ ≥ r²` cross-multiplied:
    `dm21·rSqNum ≤ dm31·rSqDen`, i.e. `x = (ρ−r²)/(ρ−1) ≥ 0`.
    The zero-dial consistency test does NOT fire at current values. -/
theorem ratio_survives_current_fit : dm21 * rSqNum ≤ dm31 * rSqDen := by
  decide

/-- Numerator of `x = (m₁/m₂)²` in lowest working form:
    `xNum/xDen = (dm31·rSqDen − dm21·rSqNum) / ((dm31 − dm21)·rSqDen)`. -/
def xNum : Nat := dm31 * rSqDen - dm21 * rSqNum

/-- Denominator of `x`. -/
def xDen : Nat := (dm31 - dm21) * rSqDen

/-- The exact value of the `x`-numerator (arithmetic identity). -/
theorem xNum_eq : xNum = 9503619 := by decide

/-- The exact value of the `x`-denominator (arithmetic identity). -/
theorem xDen_eq : xDen = 243690000 := by decide

/-- ★ **The mass-floor bracket** — `38/1000 ≤ x ≤ 39/1000`:
    the lightest neutrino is pinned at `(m₁/m₂)² ≈ 0.039`
    (`m₁/m₂ ≈ 0.197`, `m₁ ≈ 1.7 meV`) with zero dials. -/
theorem x_bracket :
    38 * xDen ≤ 1000 * xNum ∧ 1000 * xNum ≤ 39 * xDen := by
  constructor <;> decide

/-- ★ **The kill threshold** — the largest solar splitting (units
    10⁻⁷ eV², same `dm31`) compatible with the reading:
    `⌊dm31·rSqDen / rSqNum⌋ = 770`, i.e. `Δm²₂₁* = 7.70×10⁻⁵ eV²`.
    The current best fit (741) sits ≈ 1.4σ below. -/
theorem kill_threshold : dm31 * rSqDen / rSqNum = 770 := by decide

/-- ★ **The kill line fires at 771** — a measured solar splitting of
    `7.71×10⁻⁵ eV²` (same atmospheric value) makes `x < 0`:
    the `m₃/m₂ = 5.71` reading would be falsified by arithmetic. -/
theorem kill_line_at_771 : dm31 * rSqDen < 771 * rSqNum := by decide

/-- ★★ Capstone bundle — survival + floor bracket + sharp kill line,
    one conjunction (the zero-dial falsifier core, all-ℕ). -/
theorem neutrino_mass_floor_falsifier_core :
    (dm21 * rSqNum ≤ dm31 * rSqDen)
    ∧ (38 * xDen ≤ 1000 * xNum ∧ 1000 * xNum ≤ 39 * xDen)
    ∧ (dm31 * rSqDen / rSqNum = 770)
    ∧ (dm31 * rSqDen < 771 * rSqNum) :=
  ⟨ratio_survives_current_fit, x_bracket, kill_threshold, kill_line_at_771⟩

end E213.Lib.Physics.Mixing.NeutrinoMassFloor
