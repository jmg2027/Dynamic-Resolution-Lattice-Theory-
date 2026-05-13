# `Lib/Physics/Mixing/` — flavor mixing matrices + CP violation

CKM (quark) + PMNS (neutrino) mixing matrices, Cabibbo angle,
CP violation.

## Files (5)

  - `CabibboAngle.lean`     — Cabibbo angle θ_C
  - `CKMHierarchy.lean`     — CKM mixing matrix hierarchy
  - `NeutrinoMixing.lean`   — PMNS neutrino mixing matrix
  - `CPViolation.lean`      — CP-violation parameter
  - `Bridge.lean`           — bridge to other clusters

## Where to add new files

  - Specific mixing angle      → `<Angle>Angle.lean`
  - Hierarchy / matrix         → `<Name>Hierarchy.lean` /
                                  `<Name>Mixing.lean`
  - Symmetry-breaking effect   → `CPViolation*` / `<...>Violation`
