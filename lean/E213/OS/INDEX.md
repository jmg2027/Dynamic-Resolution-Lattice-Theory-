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

## Current realisation status (Tier 4 A1, in progress)

This directory currently contains:
  - **INDEX.md** (this file) — OS layer concept + migration plan

**Migration plan** (deferred to dedicated session per the
delicate import-update requirements):

  1. `OS/HodgeConjecture/Bridges/`
     ← move from `Math/Cohomology/HodgeConjecture/Bridge/*` (7 files)
     - Tate, MumfordTate, BlochBeilinson, BeilinsonRegulator,
       BeilinsonLichtenbaum, ChernCharacter, HodgeTate
     - Downstream importers: 3 files (HodgeConjecture/API.lean +
       2 sibling Bridge files cross-import)

  2. `OS/Physics/Capstones/`
     ← move from `Physics/Capstones/*` (13 files)
     - AbsoluteAtomicCapstone, Capstone, FinalCapstone,
       FinitistObservableChain, MasterCatalog, MegaCapstone,
       Paper2Bundle, Paper3Bundle, Phase3Capstone,
       PhysicsTrackComplete, PureAtomicObservables, UltraCapstone,
       ValidationStandardOne
     - Downstream importers: 10+ files (Physics.lean + various)

## Why the move is deferred

The G12 Option γ realisation requires:
  1. `git mv` of 20 source files
  2. Namespace updates (`E213.Physics.Capstones.X` → `E213.OS.Physics.Capstones.X`)
  3. Bulk-sed of ~15 downstream `import` statements
  4. Verification: `lake build` clean + `scan_all_axioms.py`
     reports no PURE→DIRTY regression

The structural commitment is made (this INDEX.md + ARCHITECTURE.md
§1.4.5).  Actual file moves should be done in a session dedicated
specifically to the migration, with full pre/post axiom-status diff.

## Future inhabitants

Beyond the initial migration, OS/ will house:
  - Cross-discipline interface adapters (Bridge files)
  - Multi-observable orchestration capstones
  - Per-subsystem INDEX.md documentation
  - Public API entry points (e.g., `OS/HodgeConjecture/API.lean`)

See `research-notes/G12_layered_api_classification.md` §5 for the
full discussion + Option α/β/γ trade-offs.
