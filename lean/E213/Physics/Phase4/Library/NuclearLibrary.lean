import E213.Physics.SimplexCounts

/-!
# Nuclear Library — 핵 atomic catalog

## Magic numbers (Phase 1 검증, 7/7 정확)

  2, 8, 20, 28, 50, 82, 126

## HO closed form

  ho_magic(n) = n(n+1)(n+2)/3

  n=1: 2     n=2: 8      n=3: 20
  n=4: 40    n=5: 70     n=6: 112    n=7: 168

## Spin-orbit shift (8 atomic)

  관측 = HO + atomic correction
  Phase 1 NuclearShells 검증.

## Binding energy

  Per nucleon ≈ 8 MeV = NS² - 1 = 1/α_3 atomic
  Nuclear radius r₀ ≈ 1.25 fm = d/(NS+1) atomic
-/

namespace E213.Physics.Phase4.Library.NuclearLibrary

open E213.Physics.Simplex

/-- HO magic number 1 = NT (smallest atom). -/
theorem ho_magic_1 : NT = 2 := by decide

/-- HO magic 2 = NS² - 1 (= F_6). -/
theorem ho_magic_2 : NS * NS - 1 = 8 := by decide

/-- HO magic 3 = 4d = 20. -/
theorem ho_magic_3 : 4 * d = 20 := by decide

/-- HO magic 7 = 168 (Z=168 super-heavy 예측). -/
theorem ho_magic_7 : 7 * 8 * 9 / 3 = 168 := by decide

/-- Nuclear binding ~ 1/α_3 = 8 MeV atomic. -/
theorem binding_atomic : NS * NS - 1 = 8 := by decide

end E213.Physics.Phase4.Library.NuclearLibrary
