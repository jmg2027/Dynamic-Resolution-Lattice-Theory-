# `lean/E213/OS/` — Operating System layer (★ G12 §5)

The orchestration layer of 213's vertical architecture.  Where
**Hypervisor** provides the single Lens *abstraction* (Raw → α
catamorphism), **OS** *composes multiple Lens-derived subsystems*
into stable APIs that downstream applications consume.

## Layer position

```
Kernel       — bare computation (Lean-internal substrate)
Firmware     — axiom + forced-uniqueness commitment
Hypervisor   — view/abstraction mechanism (Lens type + catamorphism)
Meta         — metatheorems ABOUT Hypervisor
OS  ★        — orchestration: stable API, subsystem composition,
               cross-domain interface adapters
App          — concrete instance (single observable, single theorem)
```

OS and Meta are **parallel**, not sequential:
  - Meta = *propositions* about Hypervisor ("for all Lens, …")
  - OS = *compositions* of Hypervisor ("Cup-Lens × Hodge-Lens
    orchestrated into HC²¹³ subsystem with public API")

## Current realisation status (Tier 4 A1, ✔ COMPLETE)

This directory currently contains:
  - **INDEX.md** (this file) — OS layer concept + migration record
  - **HodgeConjecture/Bridges/** (7 files) — cross-discipline
    interfaces for HC²¹³ (migrated 2026-05-XX)
  - **Physics/Capstones/** (13 files) — physics-track orchestration
    capstones (migrated 2026-05-XX)

## Migration record (2026-05-XX)

  1. `OS/HodgeConjecture/Bridges/` ← from
     `Math/Cohomology/HodgeConjecture/Bridge/*` (7 files)
     - Tate, MumfordTate, BlochBeilinson, BeilinsonRegulator,
       BeilinsonLichtenbaum, ChernCharacter, HodgeTate
     - Verification: `hodge_conjecture_213_complete` PURE,
       `tate_213_5_1` PURE, lake build clean

  2. `OS/Physics/Capstones/` ← from `Physics/Capstones/*` (13 files)
     - AbsoluteAtomicCapstone, Capstone, FinalCapstone,
       FinitistObservableChain, MasterCatalog, MegaCapstone,
       Paper2Bundle, Paper3Bundle, Phase3Capstone,
       PhysicsTrackComplete, PureAtomicObservables, UltraCapstone,
       ValidationStandardOne
     - Downstream importers updated: `Physics.lean`,
       `Math/Cohomology/DiamondAudit.lean`,
       `Physics/Foundations/DrltZeroParameters.lean`,
       `Physics/Couplings/MasterUnification.lean` (+
       fixed pre-existing typo `YangMills.Gap.Bridge`
       → `YangMills.Bridge` from commit 69a3b08)
     - Verification: `master_atomic_catalog`, `drlt_physics_milestone`,
       `phase1_absolute`, `master_capstone`,
       `drlt_zero_parameter_claim` all PURE; whole-repo
       `lake build` clean

## Future inhabitants

Beyond the initial migration, OS/ will house:
  - Cross-discipline interface adapters (Bridge files)
  - Multi-observable orchestration capstones
  - Per-subsystem INDEX.md documentation
  - Public API entry points (e.g., `OS/HodgeConjecture/API.lean`)

See `research-notes/G12_layered_api_classification.md` §5 for the
full discussion + Option α/β/γ trade-offs.
