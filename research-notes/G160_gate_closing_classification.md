# G160 — Gate-closing classification: which orphan clusters to wire / purify / delete

**Tier-1.**  Makes the G159 build-gate-hole remediation *actionable*.  The
gate-closing was flagged as a "deliberate decision"; this note shows the
decision is mostly mechanical — **most orphans are already-closed results
that simply were never imported into the `Lib/Math.lean` / `Lib/Physics.lean`
umbrellas** — with a small minority genuinely needing a judgement call.

## The gate (recap, from G159)

`tools/full_build.sh` compiles only what is reachable from the three roots
`{E213, Lib.Math, Lib.Physics}`.  ~326 modules (~21%) are orphaned: built
only when explicitly targeted.  Gate-closing = wire the permanent ones into
an umbrella (or flip `lakefile` `globs` to build all submodules once the
tree is clean).

## Classification rule

For each orphan cluster, the decision is determined by three read-only
signals:
  1. **Has a `theory/` chapter?** → it is a *promoted / closed* topic →
     **GATE** (it is a permanent result; being un-wired is the accident).
  2. **Builds clean + ∅-axiom?** → GATE directly.  **Builds but dirty?** →
     **PURIFY-then-GATE** (apply the G159/Px purification pattern first).
  3. **No chapter, superseded, or experimental WIP?** → candidate **DELETE**
     (or leave explicitly out-of-gate with a marker).

## Per-cluster verdict (orphan count; theory chapter; build/purity status)

| Cluster | n | theory chapter | build (probed) | verdict |
|---|---|---|---|---|
| `Cohomology.Bipartite` | 49 | `cohomology/k_nm_c_classification` etc. | — | **GATE** (c-counter programme, closed) — scan purity first |
| `Cohomology.Fractal` | 25 | `cohomology/fractal.md` | — | **GATE** (ConfigCount lives here; mostly PURE) |
| `Cohomology.{Cup,CupAW}` | 17 | cohomology/* | — | **GATE** (cup-ring machinery) |
| `Mobius213.Px` | 26 | `mobius213_p_orbit_closure.md` | green | **PURIFY-then-GATE** — in progress (QFib/FibCassini/ConvergentDet/MobiusSelfForm done; PGeneratesNat ongoing) |
| `CayleyDickson.{Integer,Tower,Levels,Lipschitz}` | 28 | `algebra_tower`, `exotic_4mfd_cork` | `AlgebraTowerCapstone` green | **GATE** (CD tower, closed) — scan purity |
| `SignedCut.{Octonion,Core,Bridge,CD,Hurwitz}` | 25 | `signed_cut.md` | heads green | **GATE** (5²⁵-ceiling tail already deleted) |
| `HodgeConjecture.Refinement` | 5 | `cohomology/hodge_conjecture.md` | `HodgeConjecture` green | **GATE** |
| `Real213.{ExpLog,…}`, `Analysis.{DyadicSearch,FluxMVT}` | ~10 | `real213.md`, analysis | — | **GATE** (real-number arc) |
| `AlphaEM/{GramStructural*,CupLadder*,…}` | ~13 | `physics/alpha_em/*` | green (precision PURE) | **GATE** — `GramStructuralCapstone` already wired; do the rest |

**Net**: the dominant action is *GATE* — wiring closed results that were
accidentally left out of the umbrella.  Only `Mobius213.Px` is known-dirty
(being purified).  DELETE candidates are rare and must be confirmed
file-by-file (no chapter + superseded); none identified wholesale here.

## Mechanism

  - **Wire**: add `import E213.Lib.Math.<ClusterHead>` to `Lib/Math.lean`
    (or `Lib/Physics.lean`), one cluster head at a time, rebuilding the
    umbrella after each to catch any latent rot the gate had hidden.
  - **Pre-req per cluster**: `lake build <head>` green AND
    `tools/scan_axioms.py` clean (or purified first).  Gating a dirty
    cluster is build-safe but imports a purity-debt into the official gate —
    so purify before wiring (per the user directive "category-3 → all PURE").
  - **End state**: once the orphan set is the intended-empty, switch
    `lean_lib E213` `globs` to build all submodules so the hole cannot
    reopen, and make the glob the canonical `full_build.sh` gate.

## Caveats / what still needs a real decision

  - **Purity unknown** for most clusters until scanned — a cluster that
    looks closed may carry `omega`/`Nat.mul_assoc`/`simp` dirt (cf. Px).
    The G159 purification pattern applies, but the volume is unknown.
  - **Genuinely-dead files**: the ~111 orphans with *no importer at all*
    (G159) include both umbrella heads (keep) and possibly abandoned WIP
    (delete) — needs a per-file pass, not a cluster verdict.
  - This note is read-only-derived; build/purity columns marked "—" were not
    re-scanned this pass (agent holds the build lock).

## Pointers
  - Gate-hole map: `research-notes/G159_build_gate_hole_orphan_audit.md`.
  - Purification pattern: `G159` + `HANDOFF` ("reusable purification pattern").
  - Umbrellas: `lean/E213/Lib/Math.lean`, `lean/E213/Lib/Physics.lean`,
    `lakefile.toml`, `tools/full_build.sh`.
