import E213.Physics.Phase4.Library.IE
import E213.Physics.Phase4.Library.Field
import E213.Physics.Phase4.Library.Material
import E213.Physics.Phase4.Library.Mixing
import E213.Physics.Phase4.Library.Astro
import E213.Physics.Phase4.Library.Methodology

/-!
# Phase 4 Library — atomic catalog (consolidated 27 → 6 files, 2026-05-01)

★ User directive ★
"Write a complete methodology for computing all IEs this way + periodic table
from scratch.  Organize as library + catalog.  Other physics + math too as a
giant library."

## Layout (post-2026-05-01 consolidation)

  IE.lean           — IEMethodology, AtomicFunctions, PeriodicCatalog
                       (Z=1-36), Period{5,6,7}IE, CompletePeriodicTable
  Field.lean        — QFT, QG, GR, StatPhys, Information, Optics,
                       CondensedMatter, Topology, Particle (9 sub-namespaces)
  Material.lean     — AtomicMass, Coupling, Hadron mass, Lepton mass,
                       Molecular catalogs (5 sub-namespaces)
  Mixing.lean       — CKM + PMNS (2 sub-namespaces)
  Astro.lean        — Cosmology + Nuclear (2 sub-namespaces)
  Methodology.lean  — Math + Geometry (2 sub-namespaces)

Each merged file preserves the original namespaces under
`E213.Physics.Phase4.Library.<TopicName>` for backward
compatibility with downstream `#print axioms` references.

## Original organization (pre-consolidation, recoverable from git)

The pre-consolidation tree had 27 small files (each 27-69 lines)
with the same `import E213.Physics.Simplex.Counts` and 2-5
`by decide` theorems per file.  Consolidated 2026-05-01 (commit
to come) — see git log for the per-file recovery if needed.
-/
