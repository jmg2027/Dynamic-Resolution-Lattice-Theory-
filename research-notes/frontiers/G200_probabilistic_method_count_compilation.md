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

## The concrete lift — DONE for the per-event count (the "why")

`Lib/Math/Combinatorics/RamseyLowerBound.lean` (∅-axiom) builds the *reason*
the per-event count is `2·2^{E−m}`, which is the whole content of "why the
probabilistic method counts what it counts":

  - ★ **`count_factor`** — `bcount (fun l => p (l.drop r)) (allBoolLists (r+m))
    = 2^r · bcount p (allBoolLists m)`.  A predicate blind to the `r` prepended
    bits counts `2^r ·` (its count on the suffix).  **The why:** each free edge
    is one distinguishing, and a distinguishing *doubles* the residue — so
    existence-counting **factors** because independent distinguishings
    multiply.  This is COUNT's multiplicativity, the residue-level reason.
  - ★ **`mono_event_count`** — `bcount (fun l => isConst (l.drop r))
    (allBoolLists (r+(m+1))) = 2^(r+1)`.  Per-event `= 2^r · 2`: `count_factor`
    (free edges) × `BoolEnum.bcount_const` (the `2` shared colours).  Exactly
    Erdős' `2·2^{E−C(k,2)}`, `E = r + C(k,2)`, derived not asserted.

Both `#print axioms → "does not depend on any axioms"`.

### Arbitrary-subset count — DONE, with an observation (`matchesC_count`)

The naive plan for an arbitrary (scattered) `k`-subset was "relabel edges to a
suffix, invoke permutation-invariance of `bcount`".  Doing it directly yielded a
better route + an observation:

  - ★ **`matchesC_count`** (∅-axiom) — model the constraint per-position as
    `Option Bool` (`some b` fixes, `none` free); then
    `bcount (matchesC c) (allBoolLists c.length) = 2 ^ countNone c` for an
    **arbitrary** interleaving of fixed/free positions.
  - **Observation:** permutation-invariance is *unnecessary*.  Each `none`
    doubles, each `some` fixes (`×1`), independent of order — so the subset may
    sit anywhere, and this *is why* permutation-invariance holds (it is a
    corollary of per-position independence, not a prerequisite).  The heavy
    list-permutation-action + enumeration-bijection machinery is sidestepped.

So `matchesC_count` subsumes `count_factor` for the per-event count of an
arbitrary `S`: monochromatic-on-`S` `= matchesC(some false on S) ∨
matchesC(some true on S)`, disjoint, count `2·2^{E−|S|}`.

**Remaining rung** (now just the `K_N` model): an edge↔position indexing and
`k`-subset enumeration giving `t = C(N,k)` events, then `erdos_schema` with
`c = 2·2^{E−C(k,2)}`, `E = C(N,2)`, `t·c < 2^E ⟺ 2·C(N,k) < 2^{C(k,2)}` closes
the *named* `R(k,k) > 2^{k/2}`.

### Cumulative half — DONE (registered in the framework)

COUNT is now registered as the **quantitative `GAP` sub-mode** (not a 9th
instruction — that would be "view promoted to identity"):

  · `seed/PROOF_ISA.md` — GAP sub-mode subsection (witness `count_existence`,
    the 72× `pigeonhole` tell, the doubling lift).
  · `lean/E213/Lib/Math/Foundations/ProofISALifts.lean` — **Archetype 4**
    COUNT / cardinality-doubling (`lift_count = count_existence`,
    `lift_count_factor = matchesC_count`, both PURE); the `GAP`-cardinality
    complement to A1's `GAP`-diagonal, *not* in `H`'s ORBIT family.
  · `theory/essays/proof_isa/probabilistic_method.md` — the full "why".

**Decision (this checkpoint):** the named `R(k,k)` closure is pure `K_N`
bookkeeping with no new "why", so it is left as the stated rung; the conceptual
payoff (the COUNT instruction + its lift archetype) is banked into the
framework, which is the experiment's actual yield.

## Reading

  - instruction set: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`
  - carrier: `lean/E213/Lib/Math/Combinatorics/BoolEnum.lean`
  - this build: `lean/E213/Lib/Math/Combinatorics/CountExistence.lean`
  - lift catalog: `lean/E213/Lib/Math/Foundations/ProofISALifts.lean`
