# Session Handoff — 2026-06-04 (proof-ISA compilation series)

## Branch
`claude/novel-math-discoveries-fMR2z` — **not pushed**, ahead of
`origin/claude/novel-math-discoveries-fMR2z` by **58 commits** (47 from the
`origin/main` fast-forward merge at the session start + 11 this session).
Working tree clean.  Each new module build-verified clean + **PURE**
(`#print axioms` empty) individually; `lake build E213` (root) clean.

> Unverified-signature hook: every commit's author is `Claude
> <noreply@anthropic.com>` (correct); the "Unverified" badge is the missing
> GPG/SSH signature, which this environment cannot produce — `amend`/`rebase`
> will NOT fix it and must not be run (would rewrite the merged main history).

## What Was Done This Session

The session began by answering "is there genuinely-new math here?" (4 rounds of
literature deep-research → verdict: the repo is, by design, mostly ∅-axiom
**re-statement**; honest novelty is thin — `K_{m,n}^{(c)}` cup-codim and the
Eisenstein cross-det were the only defensible candidates, both later down-graded
on arXiv comparison).  That re-framed the work around the repo's *actual* thesis
(`seed/PROOF_ISA.md`, merged from main): **mathematics as compilation from the
residue instruction set** — open problems are *compiled* to a shared ISA, not
cracked.  The rest of the session executed that programme.

### 1. The COUNT instruction (probabilistic method) — PURE ✓
Compiled Erdős (1947) `R(k,k) > 2^{k/2}`.  Its move (`#bad < #total ⟹ ∃ good`)
is **not** one of the eight named instructions — it is the **quantitative `GAP`
witness**, the primitive the repo already used (≈25 Lean files) as `pigeonhole`
without naming.  Registered as a **GAP sub-mode** (not a 9th instruction).
- `Lib/Math/Combinatorics/CountExistence.lean` — `union_bound`, `deficit_exists`
  (constructive finite-search extraction — why the method is ∅-axiom at all),
  `count_existence` (the instruction), `erdos_schema` (the method as one thm).
- `Lib/Math/Combinatorics/RamseyLowerBound.lean` — the per-event count's *why*:
  `count_factor` (each free distinguishing **doubles** the count → existence-
  counting factors because distinguishings multiply), `mono_event_count`
  (`2·2^{E−m}` derived), `matchesC_count` (arbitrary-subset count; **observed**:
  permutation-invariance is unnecessary, the `Option Bool` per-position model
  handles scattered subsets directly).
- Registered: `seed/PROOF_ISA.md` (GAP sub-mode), `ProofISALifts.lean`
  Archetype 4 (`lift_count`, `lift_count_factor`).

### 2. The linear-algebra (dimension) method = COUNT in a linear codomain — PURE ✓
`Lib/Math/Combinatorics/LinearDependence.lean` — `dimension_bound_is_count`:
`m>n` vectors in `𝔽₂^n` are dependent because their `2^m` subset-sums collide in
the `2^n`-value space (**pigeonhole = COUNT**); the dependency is the collision's
residue.  Reuses the *exact* COUNT witness `List213.nodup_length_le_of_subset`.
(`vsum`/`vxor` hand-rolled; `vxor_len_eq` avoids `List.length_zipWith`'s propext.)

### 3. The parity / invariant method = READ ∘ SEPARATE — PURE ✓
`Lib/Math/Combinatorics/ParityInvariant.lean` — mutilated chessboard.
`tiling_balanced` (every domino-tiling balances the two colours — a conserved
`READ`/catamorphism), `corners_same_colour` (the obstruction = `SEPARATE`).
**Not** COUNT (conservation→separation, not deficit→existence), **not** a new
instruction.  `par` reuses canonical `Mod213.parity` (`adj_par` = `parity_succ`).

### 4. König's lemma — the boundary marker (where ∅ stalls) — conditional PURE ✓
`Lib/Math/Combinatorics/KonigConditional.lean` — the first reproduction that
**stalls**.  Compiles to `LOOP ∘ ⟦DECIDE InfBelow⟧`: the path-construction is
internal (`konig_conditional`, `walk`+`walk_inf`, PURE); the stall is the oracle
= deciding `InfBelow` (`Π⁰₁`, an `LLPO`/`WKL` import).  `InfChildExists` stated,
**left unproved** (proving it as a Bool-choice IS the exterior).  Sharpened by the
corpus sweep: the residue *has* constructive infinite descent
(`CoResidue.spineL`/`allBranch`, given by definition); König's stall is the
decision about a *foreign* tree, not infinity itself.

### 5. The why-archive + corpus grounding + dedup sweep
- New `theory/essays/proof_isa/` (INDEX + 4 essays) — the "why" of each
  reproduction at the residue level.
- Grounded the "constructive interior is complete" claim in the real corpus
  (`STRICT_ZERO_AXIOM.md`: **1145 PURE / 0 real DIRTY**; number systems / a
  real-analysis course / algebra-cohomology-number-theory).
- **Corpus cross-ref sweep** (the König discipline applied to all essays):
  deduped `parNat → Mod213.parity`; corrected the `72×` pigeonhole figure to the
  verifiable ≈25 Lean files; cited the abstract pigeonhole primitives; connected
  the parity "conserved READ" to `GraphConnectivity.IsClosed`/`closed_const`
  (honestly — the domino 2-colouring is the bipartite *dual* of the same-on-edge
  δ⁰-kernel, not a literal instance).  **Lesson logged: search the corpus before
  building — it dedups and sharpens.**

## Current Precision Results (0 free parameters)
**Unchanged this session** — this was math-frontier / methodology work
(the proof-ISA compilation series), not a physics-constant edit.  Canonical
table: `catalogs/physics-constants.md` (`1/α_em` 0.09 ppb, `m_μ/m_e` 0.48 ppb,
`m_p` 0.000%, etc.).

## Open Problems (Priority Order)

### 1. Named `R(k,k) > 2^{k/2}` closure — pure `K_N` bookkeeping (no new "why")
All engine pieces built ∅-axiom (`erdos_schema` + `mono_event_count` +
`matchesC_count`).  Remaining: a `K_N` edge↔position indexing + `k`-subset
enumeration giving `t = C(N,k)` events, each `= matchesC(some false on S) ∨
matchesC(some true on S)` (count `2·2^{E−|S|}`), then feed
`t·c < 2^E ⟺ 2·C(N,k) < 2^{C(k,2)}` into `erdos_schema`.
Frontier note: `research-notes/frontiers/G200_probabilistic_method_count_compilation.md`.

### 2. (carried) Markov uniqueness kernel `H` — the orbit-realizability residue
Frobenius 1913.  ISA-localized to one named residue (uniform cross-word
continuant-trace `SEPARATE`); closest lift archetype = **ORBIT** (A3, same
family).  Frobenius continuant formula proved ∅-axiom (`markovNum_eq_cohn_trace`).
Frontier notes: `research-notes/frontiers/markov_lagrange/{G191,G192,G193,G197}*`.

## Unresolved from This Session
- The König stall (`InfChildExists`) is **deliberately** unproved — it is the
  exterior boundary, not a gap to close ∅-axiom.  Do **not** attempt to prove it
  (that would import `LLPO`/`WKL`).
- No technique reproduced this session forced a **new** instruction; the eight
  held (3 closed onto COUNT / READ∘SEPARATE, 1 stalled).  Whether a genuinely
  ISA-extending technique exists is open — candidates would be other
  non-constructive methods (compactness done; Banach–Tarski/AC, ultrafilters).

## Next
Either (a) close the named `R(k,k)` `K_N` bookkeeping (Open #1 — mechanical,
build on `erdos_schema`), or (b) compile another solved technique to keep
mapping the ISA (a method that might force a new instruction, or another
boundary-stall).  The why-archive `theory/essays/proof_isa/INDEX.md` is the
running ledger.

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: `theory/essays/proof_isa/{INDEX,probabilistic_method,
  linear_algebra_method,parity_invariant_method,konig_boundary}.md` — the why-archive
  (Tier 3), mirroring the Tier-2 Lean in `Lib/Math/Combinatorics/`.
- **Promotion candidates**: none pending (the proof-ISA Lean + essays are paired).
- **Active scratchpad**: `research-notes/frontiers/G200_*` (proof-ISA series,
  one open rung); carried Markov-`H` frontier notes.

## File Map
```
NEW Lean (all PURE, in Lib/Math/Combinatorics/):
  CountExistence.lean      ← COUNT instruction: union_bound, deficit_exists, count_existence, erdos_schema
  RamseyLowerBound.lean    ← per-event "why": count_factor, mono_event_count, matchesC_count
  LinearDependence.lean    ← dimension_bound_is_count (= COUNT in 𝔽₂ codomain)
  ParityInvariant.lean     ← tiling_balanced, corners_same_colour (= READ ∘ SEPARATE); par=Mod213.parity
  KonigConditional.lean    ← konig_conditional, walk, walk_inf (the LOOP); InfBelow/InfChildExists (the stall)
NEW theory (why-archive):
  theory/essays/proof_isa/INDEX.md + {probabilistic,linear_algebra,parity_invariant}_method.md + konig_boundary.md
MODIFIED:
  seed/PROOF_ISA.md                          ← COUNT registered as GAP sub-mode
  lean/E213/Lib/Math/Foundations/ProofISALifts.lean ← Archetype 4 (lift_count, lift_count_factor)
  research-notes/frontiers/INDEX.md          ← proof-ISA series + G200 registered
  research-notes/frontiers/G200_probabilistic_method_count_compilation.md ← the COUNT frontier note
```
