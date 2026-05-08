import E213.Lib.Physics.AlphaEM
import E213.Lib.Physics.Atomic
import E213.Lib.Physics.Basel
import E213.Lib.Physics.Capstones
import E213.Lib.Physics.Cosmology
import E213.Lib.Physics.Couplings
import E213.Lib.Physics.Foundations
import E213.Lib.Physics.Hadron
import E213.Lib.Physics.Higgs
import E213.Lib.Physics.Mass
import E213.Lib.Physics.Mixing
import E213.Lib.Physics.Nuclear
import E213.Lib.Physics.Simplex
import E213.Lib.Physics.Substrate
import E213.Lib.Physics.Symmetry
import E213.Lib.Physics.YangMills

/-! E213.Lib.Physics — DRLT physics deployment of the 213 axiom.

Importing this single module pulls in every Physics sub-tree
umbrella.  The directory tree is the spec; this file is the
top-level entry point.

Sub-trees (each = a sub-directory + a `<DirName>.lean` umbrella):

  AlphaEM       — 1/α_em(IR) = 137.036
  Atomic        — atomic-physics observables (Bohr, BondAngles, IE/)
  Basel         — Basel partial sum S(N) brackets for ζ(2)
  Cosmology     — Ω_Λ, H_0, N_eff, GravityShadow, HorizonInformation
  Couplings     — α_GUT, α_3, α_2, ColorConfinement, GUTUnification
  Foundations   — N_universe = d^(d²) cardinality + atomic constants
  Hadron        — m_p, m_n, hadron masses, ProtonG, QuarkHierarchy
  Higgs         — m_H, v_H, λ_H quartic
  Mass          — m_μ/m_e, m_τ/m_μ, hierarchy towers
  Mixing        — Cabibbo, CKM, PMNS, CP violation
  Nuclear       — Binding, DeuteronBinding, MagicNumbers, Shells
  Simplex       — Δ⁴ counts, generations, f_occ spectrum
  Substrate     — Phase 2 substrate-genesis (origin, edges, etc.)
  Symmetry      — Aut(K) group structure (C3 step 1: |Aut| = 768
                  decomposed into external Sym(NS)×Sym(NT) and
                  internal C_2^(NS·NT)); pointers to gauge group emergence
  YangMills     — SU(5) roots, WZ bosons, Weinberg angle, mass gap

Plus capstones at `OS/Physics/Capstones/`:
  PureAtomicObservables, ValidationStandardOne, FinitistObservableChain,
  PhysicsTrackComplete, MasterCatalog.
-/
