import E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy

/-!
# Sedenion zero divisors — the composition boundary made concrete

The polarization Moufang framework (`Meta/Algebra213/CDDoubleMoufang`)
closes norm composition `|u·v|² = |u|²·|v|²` exactly up to the
octonion-analog layer (Cayley / ZOmegaQuad / L4T).  One Cayley-Dickson
step further — the **Sedenion** layer (Type A L4 = `CDDouble Cayley`) —
the base is itself non-associative, `TraceNormed213` does not lift, and
composition genuinely fails.

This file exhibits the failure concretely: a pair of **non-zero**
sedenions whose product is `0`.  In the standard unit-basis `e₀..e₁₅`
the witness is `(e₁ + e₁₀)·(e₄ − e₁₅) = 0` (coordinates found for this
repo's nested CD encoding).  It is the first violation of NonVanishing
(R3) in the tower, and it makes norm-multiplicativity provably **false**
at L4 — so no `MoufangIntegerNormed213 Sedenion` can exist.  This is a
falsifier-style boundary marker, the negative companion of the
octonion-layer composition theorems.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.Sedenion

open E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy (normSq)

/-- Witness `u = e₁ + e₁₀` (nested CD encoding). -/
def zd_u : Sedenion :=
  ⟨⟨⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩,
   ⟨⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩⟩

/-- Witness `v = e₄ − e₁₅` (nested CD encoding). -/
def zd_v : Sedenion :=
  ⟨⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨1, 0⟩, ⟨0, 0⟩⟩⟩,
   ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, -1⟩⟩⟩⟩

theorem zd_u_ne_zero : zd_u ≠ 0 := by decide
theorem zd_v_ne_zero : zd_v ≠ 0 := by decide
theorem zd_mul_eq_zero : zd_u * zd_v = 0 := by decide

/-- **Sedenions have zero divisors** — NonVanishing (R3) fails at L4. -/
theorem sedenion_has_zero_divisors :
    ∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0 :=
  ⟨zd_u, zd_v, zd_u_ne_zero, zd_v_ne_zero, zd_mul_eq_zero⟩

/-- **Norm composition fails at the Sedenion layer**: `|u·v|² = 0` while
    `|u|²·|v|² = 4`.  Concrete proof that no composition-algebra (hence no
    `MoufangIntegerNormed213`) structure extends past the octonion-analog
    layer — the boundary the polarization framework reaches. -/
theorem sedenion_normSq_not_multiplicative :
    ∃ u v : Sedenion, normSq (u * v) ≠ normSq u * normSq v :=
  ⟨zd_u, zd_v, by decide⟩

end E213.Lib.Math.CayleyDickson.Levels.Sedenion
