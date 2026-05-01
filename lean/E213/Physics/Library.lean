import E213.Physics.Library.IEMethodology
import E213.Physics.Library.AtomicFunctions
import E213.Physics.Library.PeriodicCatalog
import E213.Physics.Library.AtomicMassLibrary
import E213.Physics.Library.CouplingLibrary
import E213.Physics.Library.MathLibrary
import E213.Physics.Library.CosmologyLibrary
import E213.Physics.Library.HadronMassLibrary
import E213.Physics.Library.PMNSLibrary
import E213.Physics.Library.CKMLibrary
import E213.Physics.Library.NuclearLibrary
import E213.Physics.Library.MolecularLibrary
import E213.Physics.Library.GeometryLibrary
import E213.Physics.Library.ParticleLibrary
import E213.Physics.Library.TopologyLibrary
import E213.Physics.Library.LeptonMassLibrary
import E213.Physics.Library.StatPhysLibrary
import E213.Physics.Library.QFTLibrary
import E213.Physics.Library.GRLibrary
import E213.Physics.Library.QGLibrary
import E213.Physics.Library.CondensedMatterLibrary
import E213.Physics.Library.OpticsLibrary
import E213.Physics.Library.InformationLibrary
import E213.Physics.Library.Period5IE
import E213.Physics.Library.Period6IE
import E213.Physics.Library.Period7IE
import E213.Physics.Library.CompletePeriodicTable

/-!
# Phase 4 Library — IE library + other field frameworks

★ User directive ★
"Write a complete methodology for computing all IEs this way + periodic table
from scratch.  Organize as library + catalog.  Other physics + math too as a
giant library."

## Current (IE)

  IEMethodology.lean    — IE computation procedure (8 steps)
  AtomicFunctions.lean  — reusable σ, hund_count, ...
  PeriodicCatalog.lean  — periodic table Z=1-36 atomic verification

## Future library expansion plan

### Physics Library
  AtomicMassLibrary    — atomic mass atomic chain
  HadronMassLibrary    — hadron masses (Phase 1 → library)
  CouplingLibrary      — α_em, α_GUT, α_3, ...
  PMNSLibrary          — neutrino mixing matrix
  CKMLibrary           — quark mixing matrix
  CosmologyLibrary     — Ω_Λ, η_B, H_0, T_CMB
  NuclearLibrary       — magic numbers, binding, radii
  MolecularLibrary     — bond angles, lengths, IE
  PhasesLibrary        — phase transitions, critical exponents
  ParticleLibrary      — decay rates, branching ratios

### Math Library
  PrimesLibrary        — atomic primes (2, 3, 5, 7, 13, 41, 137)
  FibonacciLibrary     — F_n atomic identifications
  CombinatoricsLibrary — C(d, k), permutations atomic
  GroupTheoryLibrary   — SU(NS), SU(NT), SU(d) atomic
  GeometryLibrary      — simplex, polytope counts
  TopologyLibrary      — cycle space, b_n, Euler char

Each library:
  * reusable atomic functions
  * catalog (organized item list)
  * Lean theorems (decide-checked)

Together: a giant atomic library.
-/
