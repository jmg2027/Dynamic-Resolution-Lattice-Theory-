# G159 — The build gate has a hole: ~350 orphaned modules

> **RESOLVED (this session)**: the hole is closed.  All latent breakage the
> orphans hid was fixed (Px subtree, AkbulutCork/InvolutionCapstone, SignedCut,
> G39Capstone, the 7 gated-build failures, and the last two —
> `EnrichedKNSNTcEvenEven`, `PellOrbitInstances`).  **`tools/full_build.sh` now
> builds every module under `lean/E213` (all 1532, exit 0)**, so no orphan can
> hide breakage anymore.  Fast `lake build E213` (framework) is kept for
> iteration.  The crown-jewel α_em precision chain was also wired into the
> umbrella.  History below.

**Tier-1.**  A static-reachability audit of the Lean import graph found
that **about 23% of `E213/**.lean` modules are not built by the standard
gate** (`tools/full_build.sh`).  Some are silently rotted; the headline
α_em precision theorem was among the ungated.  This note maps the hole and
a remediation path.

## How the gate actually works

`lakefile.toml` declares one `lean_lib E213` with no explicit `globs`, so
the default build target is the **root module `E213.lean`'s import
closure** — which `E213.lean` restricts to the framework rings
(Term / Theory / Lens / Meta + Pigeonhole), ~275 modules.

`tools/full_build.sh` adds `lake build E213.Lib.Math E213.Lib.Physics` —
the closures of the two content umbrella modules `Lib/Math.lean` and
`Lib/Physics.lean`.  So the **true gate = reachable from any of the three
roots** `{E213, E213.Lib.Math, E213.Lib.Physics}`.

A module is **orphaned** iff no chain of `import`s from those three roots
reaches it.  `lake build E213` / `full_build.sh` never compile it; it is
built only when something explicitly targets it (e.g. `scan_axioms.py
<module>`).

## The hole

  - Total `E213` modules: **1543**.  Reachable from the 3 roots: **~1190**.
    **Orphaned: ~350 (≈23%)**.
  - Of the orphans: **111** have *no importer at all* (dead/umbrella/capstone
    heads); **219** are imported only by other orphans (cluster bodies);
    **0** are imported by a reachable module (consistent — that is the
    definition).

### Two harms

  1. **Silent rot.**  An orphan can stop compiling and nothing notices.
     Confirmed this session in `Mobius213/Px/`: `ConvergentDet.lean`
     (undefined `convergent_det'`, a `conv` parse error, a `rw [h1,h2]`
     defeq bug) and `MobiusSelfForm.lean` had no `.olean` and did not
     build; `PGeneratesNat.lean` is still broken (type mismatch + omega
     failures).  All escaped `full_build.sh`.
  2. **Ungated-but-correct.**  Important results that *do* build but are
     not in any umbrella closure — e.g. the **0.2 ppb α_em precision
     chain** `AlphaEM/GramStructural{,Bracket,Newton,Capstone}`
     (`invAlphaEm_precision_theorem`) was orphaned: `AlphaEM.lean`
     imported `GradedFormulaPrecision`/`GramSelfConsistency`/`GramHigherOrder`
     but not `GramStructuralCapstone`.  Wired in this session (one import).

## Orphan clusters (by sub-tree)

Largest: `Cohomology.Bipartite` (~49), `Cohomology.Cup` (~26),
`Mobius213.Px` (~26), `Cohomology.Fractal` (~25),
`CayleyDickson.{Integer,Tower}` (~26), `SignedCut.*` (~31), `Padic` (~27),
`Real213.*` probe-twist / valid-cut files (~30), `AlphaEM` Gram/Cup-ladder
(~14), `Symmetry` (~6).  Many are whole sub-clusters whose **umbrella /
capstone head is simply not imported by `Lib/Math.lean` or
`Lib/Physics.lean`**.

### Natural re-wire points (orphan heads that pull in many orphans)

`Mobius213.Px` (+25), `CayleyDickson.Tower.AlgebraTowerCapstone` (+17),
`AkbulutCork` (+8), `Padic` (+8), `Mobius213GrandUnification` (+7),
`CayleyDickson.Tower.{UniversalOrderGrowth,TowerFixedPoint,UniversalInduction}`,
`Cohomology.Fractal.PisanoGridCapstone` (+6), `Mobius213CrossDomainMeta` (+6),
`SignedCut.Level.G38FinalCapstone` (+5), `Cohomology.K33Unified` (+4).
Importing a head into the right umbrella reconnects its whole cluster — *if
the cluster builds*.

## Remediation

**End state**: change the lib so nothing escapes — give `lean_lib E213`
`globs` that build all submodules (so `lake build` compiles the whole tree)
**OR** make `Lib/Math.lean` + `Lib/Physics.lean` transitively import every
submodule.  Either makes the gate total.

**But** the glob cannot be flipped until the rot is cleared — ~350 orphans
are not all green today (the `Px` cluster alone has ≥3 broken files).  So:

  1. Per orphan cluster head (above), attempt to build it; if green, wire it
     into the appropriate umbrella (`Lib/Math.lean` / `Lib/Physics.lean` /
     a sub-umbrella) and commit — incrementally shrinking the hole.
  2. Where a head is rotted, fix the proofs first (statements sacrosanct),
     then wire.  Track genuinely-dead/superseded files for deletion rather
     than gating.
  3. When the orphan set is empty, switch the lib `globs` to build all
     submodules so the hole cannot reopen, and update `full_build.sh` /
     CLAUDE.md to make the glob build the canonical gate.

## Done this session

  - Wired the α_em precision chain into the gate (`AlphaEM.lean` imports
    `GramStructuralCapstone`).
  - Fixed `Mobius213/Px/{ConvergentDet,MobiusSelfForm}.lean` (build).
  - `Mobius213/Px/` full-umbrella repair in progress (separate worker);
    `PGeneratesNat.lean` + any siblings to follow.

## Pointers

  - Gate: `lakefile.toml`, `E213.lean`, `Lib/Math.lean`, `Lib/Physics.lean`,
    `tools/full_build.sh`.
  - Rot examples: `Mobius213/Px/{ConvergentDet,MobiusSelfForm,PGeneratesNat}`.
  - Reproduce the audit: BFS the `^import E213\.` edges from the three roots
    over all `E213/**.lean`; the complement is the orphan set.
