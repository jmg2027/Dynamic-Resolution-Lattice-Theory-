# Session Handoff — DRLT 213

Branch: `claude/topology-precision` (UniverseChain marathon).

## Current state (2026-05-08)

`lean/E213/Lib/Math/UniverseChain/` — 13 files, ~57 ∅-axiom
theorems verified.  The deductive chain *pointing → atomicity →
5 + recurrence* is **rigorously closed**.

### What's proven (∅-axiom)

**Step 0 — Residue / generation rule** (`Residue.lean`):
  * G29 point 3 formalised as `slash : Raw → Raw → _ → Raw`
    output-type-as-Raw.  Recursion automatic from constructor.

**Steps 1–5 — Atomicity → N_U** (existing chain):
  * `Atomicity.lean`: `Atomic n ⟺ n = 5`
  * `Decomposition.lean`: `5 = 2·1 + 3·1` unique alive
  * `PairAxes.lean`: `(NS, NT) = (3, 2)` forced (`pair_forcing`
    cleaned to ∅-axiom this session)
  * `Recursion.lean`, `Universe.lean`, `Synthesis.lean`: chain bundle

**Raw enumeration / recurrence** (this session's main work):
  * `RawDepthCount.lean`: depth ≤ 2 = **5** Raws (matches d = 5)
  * `RawBipartition.lean`: leftmost-atom partition (3, 2) — flagged
    as *non-canonical* (one of many possible partitions)
  * `RawDepth3.lean`: depth ≤ 3 = 12 Raws; (3, 2) ratio breaks
    at higher depth → (8, 4)
  * `RawRecurrence.lean`: **clean recurrence
    `|S_n| = 2 + C(|S_{n-1}|, 2)`** — corrects earlier
    `a_{n+1} = a_n + C(a_n, 2)` guess
  * `RawEnumeration.lean`: **GENERAL THEOREM ∀n —
    `(enumTreeDepth n).length = rawCount n`** — induction proof,
    avoids Lean-core propext leaks via `myLengthAppend`/`myLengthMap`
  * `RawCountGeneric.lean`: N-generic recurrence
    `|S_n| = N + C(|S_{n-1}|, 2)` for arbitrary atom count

### What was retired this session

  * Earlier *Gödel/Lawvere* marathon (3 commits) reverted —
    framing required Raw-universal-Lens grounding for every term;
    deferred as too heavy.  PairForcing ∅-axiom cleanup retained.

### Solid base (won't drift)

```
[pointing → atomicity → d = 5]    ✅ proven
[5 = NS + NT = 3 + 2]              ✅ proven
[arity = 2 forced]                 ✅ proven (ArityForcing)
[recurrence |S_n| = N + C(|S_{n-1}|, 2)]  ✅ proven (general n)
[N = 2 unique minimum]             ✅ proven (§4.2 + AxiomMinimality)
```

This base is **rigorously closed and physics-solid up to 4D
projection + chirality emergence** (per AutKChiral).  Three open
programs remain.

---

## Open programs (next-session marathons)

### Marathon A — Mathematical closure (replace physics observation)

**Problem**: `TopologyCompare.lean` selects K_{3,2}^(c=2) among
bipartite candidates because `b_1 = 8 = 1/α_3` (physics
observation).  This is **empirical selection**, not pure derivation.

**Goal**: derive K_{3,2}^(c=2) from atomicity-internal arguments
alone, without invoking physics observation.

**Sub-tasks**:
  1. Prove `b_1 = NS² - 1` is forced by atomicity (currently
     `Counts.inv_alpha_3_confined : NS · NS - 1 = 8` is `decide`,
     but the *interpretation as Betti* is post-hoc).
  2. Prove c = 2 (multiplicity) from chirality / NT structure
     (currently `c` appears in TopologyCompare with no
     atomicity-internal derivation).
  3. Show K_{3,2}^(c=2) is the *unique* (NS, NT, c) bipartite
     multigraph satisfying atomicity-internal constraints —
     without `b_1 = 8` as input.

**Critical files**:
  * `lean/E213/Lib/Math/Cohomology/TopologyCompare.lean`
  * `lean/E213/Lib/Math/Cohomology/Bipartite/V32.lean`
  * `lean/E213/Lib/Physics/Simplex/Counts.lean`

**Difficulty**: high.  May require new typeclass for
"atomicity-internal Betti" or proven fact that 1/α_3 = NS² - 1
is structurally forced rather than empirically matched.

---

### Marathon B — Graph theory formalisation

**Problem**: K_{3,2}^(c=2) ⊂ Δ⁴ relationship currently only at
underlying-edge level (`UniverseChain.BipartiteFractal.bip_edge_in_K5`).
Multigraph version refuted (`multiplicity_lost`).  `research-notes/
G1_universal_lens.md` *conjectures* "any 5 elements force
K_{3,2}^(c=2)" but no formal proof exists.

**Goal**: formalise K_{3,2}^(c=2) inevitability + structural
relationships to Δ⁴ + graph-theoretic foundations.

**Sub-tasks**:
  1. Prove "any 5 elements satisfying atomicity-derived constraints
     form K_{3,2}^(c=2)" — uniqueness up to isomorphism.
  2. Vertex-transitivity / automorphism analysis of K_{25} (level
     2 fractal); extend `AutKChiral.lean` to K_{5^L}.
  3. Formalise Kuratowski-style result: K_5 = first non-planar
     coincides with d = 5 from atomicity (currently a numerical
     "signature").
  4. K_{3,2}^(c=2) as Cayley-type graph with internal labelling
     (each vertex = its slash-tree).

**Critical files** (existing):
  * `lean/E213/Lib/Math/Cohomology/Bipartite/V32.lean`
  * `lean/E213/Lib/Math/Cohomology/K5.lean`
  * `lean/E213/Lib/Physics/Symmetry/AutKChiral.lean`
  * `research-notes/G1_universal_lens.md` (conjecture)

**Difficulty**: medium-high.  Graph-isomorphism uniqueness needs
combinatorial enumeration; planarity formalisation is non-trivial
∅-axiom.

---

### Marathon C — Fractal theory formalisation

**Problem**: `numV L = 5^L` is *defined* recursively
(`Cohomology/Fractal/Level.lean`).  "Each vertex of Δ⁴ becomes a
Δ⁴" is *postulated* in `NUniverseFromFractal.lean` docstring.
`L = d² = 25` as "self-referential level" is *named*, not derived.
N_U = 5²⁵ thus rests on a chain of *definitions*.

**Goal**: formalise fractal self-similarity as a *fixed-point
theorem*, not a definition.

**Sub-tasks**:
  1. Define a self-similar map `F : Δ⁴ → Δ⁴ ⊗ Δ⁴` (vertex
     replacement) and prove it's a fixed-point of some natural
     transformation.
  2. Prove `L = d²` is the *unique* self-referential closure
     level (currently `universe_level_eq_gram` is `rfl`, ie. just
     renaming).
  3. Prove `N_U = 5^25` is *forced* (not chosen) — perhaps as
     unique cardinality where local + global structure coincide.
  4. Connect to `RawEnumeration.enumTreeDepth_length`: relate Raw
     inhabitant count to fractal vertex count at appropriate
     depth.

**Critical files**:
  * `lean/E213/Lib/Math/Cohomology/Fractal/{Level, V25}.lean`
  * `lean/E213/Lib/Physics/Foundations/{NUniverseFromFractal,
     NUniverseFractalDepth, FractalLensCardinality}.lean`
  * `lean/E213/Lib/Math/UniverseChain/RawEnumeration.lean`

**Difficulty**: highest.  Fixed-point theorems on graph
endomorphisms + uniqueness up to isomorphism + closure level
characterisation — these are deep graph/category theory.

---

## Suggested execution order

A → C → B  (or in parallel if scope allows).

  1. **A first**: replacing `b_1 = 8` physics observation with
     atomicity-internal derivation of NS² - 1 is the *narrowest*
     gap and would unlock TopologyCompare's claim.
  2. **C second**: fractal self-similarity is the *biggest open
     question* — without it the whole `5²⁵` story is definitional.
  3. **B last**: graph-theoretic foundations support both A and C,
     could be developed alongside but isolated.

Each marathon ends with: per-theorem `#print axioms` ∅, full
`lake build E213` clean, separate commit per file.

---

## Verification status (current branch)

| Check | Result |
|---|---|
| `lake build E213.Lib.Math.UniverseChain.RawEnumeration` | ✓ |
| Per-theorem ∅-axiom (UniverseChain ~57 thms) | ✓ |
| `Theory.Atomicity.PairForcing` (cleaned this session) | ✓ ∅-axiom |
| Branch ahead-of-origin | ✓ pushed |

## Hand-off pointers

  1. **Read first**: `seed/AXIOM/{00_nature, 02_statement, 03_form,
     07_self_reference}.md`, then `research-notes/G29_residue.md`.
  2. **Boot file**: this `HANDOFF.md`, then `CLAUDE.md`.
  3. **Architecture canonical**: `lean/E213/ARCHITECTURE.md`.
  4. **UniverseChain INDEX**: `lean/E213/Lib/Math/UniverseChain/
     INDEX.md` (extend with new marathon files).

## Key insight to preserve

The path *pointing → atomicity → 5 → recurrence* is **closed and
∅-axiom**.  Beyond that, *fractality / 5²⁵ / K_{3,2}^(c=2)
inevitability* are **definitional or conjecture**, awaiting
Marathons A, B, C.

The `pair_forcing` cleanup (this session) showed that *omega →
∅-axiom* hardening is feasible via `half : Nat → Nat`-style
structural rewrites + careful avoidance of `Nat.gcd` / `Nat.div`.

Branch **READY for next marathon**.  Solid base intact.
