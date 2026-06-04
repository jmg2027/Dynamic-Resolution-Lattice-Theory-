# G200 — compiling the probabilistic method surfaces a missing ISA primitive: COUNT

**Tier 1 (volatile), research memo.**  The experiment: take a *solved* hard
result whose proof technique is **not** among the eight named proof-ISA
instructions (`seed/PROOF_ISA.md`), compile it down, and see whether it (a)
reduces to a composition of the existing eight, or (b) forces a new primitive.

Target: **Erdős (1947), `R(k,k) > 2^{k/2}`** — the founding result of the
*probabilistic method*.  Criterion for picking it: the repo has `pigeonhole`
in 72 files but `Ramsey`/`probabilistic`/`union bound` essentially absent, and
no ISA instruction names a counting/averaging move.

## The actual proof (Erdős)

The `2`-colourings of `K_N`'s edges number `2^{C(N,2)}`.  A fixed `k`-subset
`S` is monochromatic in `2·2^{C(N,2)−C(k,2)}` of them; there are `C(N,k)`
subsets.  So colourings with *some* monochromatic `K_k` number at most
`C(N,k)·2·2^{C(N,2)−C(k,2)}`.  If that is `< 2^{C(N,2)}` — i.e.
**`2·C(N,k) < 2^{C(k,2)}`** — a colouring with no monochromatic `K_k` exists,
so `R(k,k) > N`.  This holds for `N < 2^{k/2}`.

One-line move: **`#bad < #total ⟹ a good object exists`.**

## Compilation verdict — (b), a new witness of the GAP family

Checked against the eight instructions:

  - **not `DIAGONALIZE`** — the diagonal forces an object by *distinction from
    all* (Cantor); here existence is forced by *counting deficit*, not
    distinction.
  - **`GAP` family, but a new witness.**  `GAP` = "a reading does not cover its
    codomain; the surplus is the residue."  The bad colourings *fail to cover*
    the colouring space, and the uncovered surplus is the good colouring — so
    structurally `GAP`.  **But** the existing `isa_gap` witness
    (`exists_non_lens_expressible`) supplies non-coverage *qualitatively*
    ("not every function is a fold").  Erdős needs it *quantitatively*:
    `|image| ≤ Σ|badᵢ| < |codomain|`.  That cardinality-comparison witness is
    **not built** as an ISA primitive.

So the probabilistic method = the **GAP family with a counting witness**.  Call
that witness **COUNT** (deficit ⟹ existence).  Decisive corroboration: the repo
*already uses* exactly this 72 times as `pigeonhole` — pigeonhole is the
*qualitative* COUNT (`N+1 → N` non-injective), the probabilistic union bound is
the *quantitative* COUNT, and the recurring finite→uniform **lift** counting is
the same primitive.  Compiling Erdős is what makes the un-named instruction
explicit.

The A/B placement question deferred earlier (COUNT as a GAP sub-mode vs a 9th
standalone instruction) is answered by the build: it is structurally one
GAP-arrow with a second witness — but operationally distinct enough to earn its
own reusable lemma.  Recommend registering it as a **GAP sub-mode** in
`Lens/ProofISA.lean` (avoids the "view promoted to identity" failure of
double-counting one arrow), with `count_existence` as the witness.

## Built this session — `Lib/Math/Combinatorics/CountExistence.lean` (∅-axiom)

Over the `BoolEnum` carrier (`allBoolLists n` = the `2ⁿ` 2-colourings):

  - `cond_or_le`, `bcount_or_le` — subadditivity of the count over `||`;
  - **`union_bound`** — `bcount (anyBad preds) L ≤ totalCount preds L`;
  - **`deficit_exists`** — `bcount bad L < |L| → ∃ l ∈ L, bad l = false` (the
    *constructive* extraction: finite search, no `Classical`, no LEM — this is
    why the probabilistic method is ∅-axiom at all, the "probability" being
    normalised finite counting);
  - ★ **`count_existence`** — `totalCount preds (allBoolLists n) < 2ⁿ
    → ∃ colouring avoiding every event`;
  - ★ **`erdos_schema`** — uniform form: `t = |preds|` events, each on ≤ `c` of
    the `2ⁿ` colourings, `t·c < 2ⁿ` ⟹ a colouring dodging all.

All five `#print axioms → "does not depend on any axioms"`.  `erdos_schema` is
the probabilistic method as a single ∅-axiom theorem; Erdős' Ramsey bound is the
instance `n = C(N,2)`, `t = C(N,k)`, `c = 2·2^{n−C(k,2)}`,
hypothesis `2·C(N,k) < 2^{C(k,2)}`.

## Open next rung (the concrete-instance lift)

`erdos_schema` is the reusable instruction; what remains to make the *named*
Erdős theorem fully concrete is the per-event count
`bcount (monochromatic-on-S) (allBoolLists C(N,2)) = 2·2^{C(N,2)−C(k,2)}` and
the subset enumeration `t = C(N,k)`.  These are finite counting lemmas (number
of Bool lists constant on a fixed sub-position-set) — additive, ∅-axiom, but a
multi-step build.  This is exactly a **finite→uniform lift** of the
`COUNT` instruction; logging it in the `ProofISALifts` catalog is the
cumulative half of the workflow.

## Reading

  - instruction set: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`
  - carrier: `lean/E213/Lib/Math/Combinatorics/BoolEnum.lean`
  - this build: `lean/E213/Lib/Math/Combinatorics/CountExistence.lean`
  - lift catalog: `lean/E213/Lib/Math/Foundations/ProofISALifts.lean`
