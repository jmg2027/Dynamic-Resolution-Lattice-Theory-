# Session Handoff — 2026-06-07

## Branch
`claude/substrate-synthesis-count-zq9K0` — pushed; `origin/main` merged in
(quadratic reciprocity + Ricci/PDE work present).  About to merge to `main`.
`cd lean && lake build` ✓ clean (full tree); `tools/layer_audit.py` 0 violations;
`tools/kernel_regress.sh` 45/45 0-axiom.  Pre-merge audit: **READY TO MERGE**.

## What Was Done This Session

### 1. Chain/antichain duality on `2^[n]` — Mirsky + Dilworth FULLY CLOSED (`ChainAntichain`, 84/84 PURE)
The de Bruijn–Tengbergen–Kruyswijk symmetric chain decomposition, end-to-end ∅-axiom:
- **`scd_sym`** — the symmetric-level invariant: every chain's `cardB` values form
  the centred run `[k,…,n−k]` with `2k+|C|=n+1` (`extendC_sym`/`raiseC_sym` + length
  helpers + `raise_sum_arith`).
- **`sym_span`/`scd_has_middle`/`scd_middle_unique`** — each chain meets the middle
  layer `⌊n/2⌋` exactly once.
- **`scd_same`/`scd_disjoint`/`scd_nodup`** — the SCD is a partition (shared vector ⟹
  same chain).  Key insight: **no `extendC`/`raiseC` injectivity needed** — `raiseC`
  is not injective; collisions die by IH disjointness.  Infra: `mem_extendC`/
  `mem_raiseC`/`child_tail_mem`, `extendC_raiseC_disjoint`, `scd_chain_nodup`
  (`consec_nodup` + `nodup_of_nodup_map`), `scd_vec_length`, `nodup_filter` (propext-free).
- **`scd_card`** — `|scd n| = C(n,⌊n/2⌋)` via the nodup middle-layer trace.
- **`dilworth_boolean`** — min chain cover `= C(n,⌊n/2⌋) =` max antichain (Sperner).
- **`sperner_via_scd`** — Sperner from the partition (a third ∅-axiom proof, after the
  LYM double count and `sperner_via_lym`).
- **`scd_flat_length`** — the SCD partitions all of `2^[n]`: `C(n,⌊n/2⌋)` chains hold
  every one of the `2^n` subsets.

### 2. Promotion + essays (three-tier discipline)
- `theory/essays/proof_isa/chain_antichain_duality.md` — the "why" of Mirsky/Dilworth
  as Sperner's dual (SEPARATE on the dual relation + COUNT; the SCD as a COUNT object
  whose count is its partition).
- `theory/essays/synthesis/duality_as_one_transpose.md` — "What is duality, in 213?":
  one SEPARATE instruction read on a relation and its swap; the duality theorem is
  `sumOver_swap` on one 0/1 incidence with a per-axis SEPARATE cap.

### 3. Merge marathon hygiene
- Merged `origin/main` (quadratic reciprocity, Ricci/PDE).
- `/process` — sink rule 1→0 (BollobasSetPair docstring decoupled), frontier updated,
  promotion log row 13.
- `/org-audit` — current-state docstrings (dropped stale "frontier/remain" tails),
  essay count 58→63.
- `/purity-check` — sorry/axiom/native_decide/Classical/Mathlib all 0; QR 11/11 PURE.
- `/ready-to-merge` — all phases green, verdict READY.

## Current Precision Results (0 free parameters)
Unchanged this session (pure combinatorics / number theory; no physics observable
touched).  Physics constants table: `catalogs/physics-constants.md`.

## Open Problems (Priority Order)
### 1. Leibniz determinant over `perms`
`Linalg213/Permutation` has `LPerm` equivalence + inversion-sign but no enumeration;
`perms` + `mem_perms_iff` + `perms_nodup` supply the index set for
`det = Σ_{σ∈perms} sign(σ)·Π M i σ(i)` — a bridge between the two permutation
developments.  Frontier note: `research-notes/frontiers/count_substrate_synthesis.md`.

### 2. A clean strict-order/pow `Meta/Nat` suite
`Nat.mul_lt_mul_right` carries **Classical.choice**; `Nat.pow_add`/`Nat.succ_sub`
carry propext — re-proven ad-hoc per file.  Canonicalise propext-free
`mul_lt_mul_right`/`pow_add`/`succ_sub`/strict-mono into `Meta/Nat`.
Frontier note: `research-notes/frontiers/count_substrate_synthesis.md`.

### 3. Abstract the COUNT duality meta-theorem
"Every finite duality = `sumOver_swap` on a 0/1 incidence + a SEPARATE cap per axis"
is witnessed (Sperner, Mirsky, Dilworth, LYM, Bollobás) but not abstracted into one
Lean theorem quantifying over incidences and caps.
Frontier note: `research-notes/frontiers/count_substrate_synthesis.md`.

## Unresolved from This Session
None — every started unit closed ∅-axiom and was committed.  The Dilworth upper
bound, flagged in earlier handoffs as "best with fresh context / ~100+ line
disjointness", was fully closed (the `scd_same` positive-disjointness induction
sidestepped the `raiseC`-injectivity dead end).

## Next
Pick up Open Problem #1 (Leibniz determinant over `perms`) or #2 (`Meta/Nat`
strict-order suite); or harvest a new domain (primacy = breadth).

## Three-tier state
- **Promotions this session**: `theory/essays/proof_isa/chain_antichain_duality.md`
  ← the closed `ChainAntichain` Mirsky/Dilworth sub-tree (logged: promotion_essay_log
  row 13).  `theory/essays/synthesis/duality_as_one_transpose.md` (essay, row 14).
- **Promotion candidates**: none outstanding for the COUNT arc (LYM/Bollobás/Sperner/
  Mirsky/Dilworth all have theory narrative).
- **Active scratchpad**: `research-notes/frontiers/count_substrate_synthesis.md`
  (kept active — open seeds above).

## File Map
```
lean/E213/Lib/Math/Combinatorics/ChainAntichain.lean  ← Mirsky + Dilworth + SCD, 84/84 PURE (this session: §9–15 — scd_sym, partition, scd_card, dilworth_boolean, sperner_via_scd, scd_flat_length)
lean/E213/Lib/Math/Combinatorics/BollobasSetPair.lean ← docstring decoupled from research-notes (favour-count discharged in BollobasCount)
theory/essays/proof_isa/chain_antichain_duality.md    ← NEW: Mirsky/Dilworth narrative (the dual of Sperner)
theory/essays/synthesis/duality_as_one_transpose.md   ← NEW: "What is duality, in 213?"
theory/essays/{INDEX, proof_isa/INDEX}.md             ← essay entries + count 63
lean/E213/Lib/Math/Combinatorics/INDEX.md             ← ChainAntichain row updated (Dilworth closed)
STRICT_ZERO_AXIOM.md                                  ← ChainAntichain 84/84 PURE entry
research-notes/frontiers/{INDEX,count_substrate_synthesis}.md ← COUNT arc closed + open seeds
research-notes/promotion_essay_log.md                 ← rows 13 (promotion), 14 (essay)
```
