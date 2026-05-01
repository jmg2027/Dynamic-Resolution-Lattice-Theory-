import E213.Physics.Simplex.Counts

/-!
# Particle Library — particle physics atomic catalog

## Decay rates

  Muon lifetime prefactor 192 = (NS²-1)(d²-1) atomic
  Z partial widths count = 2·NS·NT = 12

## Branching ratios

  Higgs BR(H→bb) ≈ 0.58 ≈ NS/d atomic
  Z → 3 lepton + 3 ν + 6 quark = 12 = 2·NS·NT

## Lifetimes / Cross-sections atomic
-/

namespace E213.Physics.Library.ParticleLibrary

open E213.Physics.Simplex.Counts

/-- Muon lifetime prefactor 192 = (NS²-1)·(d²-1) atomic. -/
theorem muon_lifetime_192 : (NS * NS - 1) * (d * d - 1) = 192 := by decide

/-- Z partial count = 2·NS·NT atomic. -/
theorem z_partial_count : 2 * NS * NT = 12 := by decide

end E213.Physics.Library.ParticleLibrary
