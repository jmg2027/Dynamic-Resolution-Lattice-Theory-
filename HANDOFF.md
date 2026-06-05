# Session Handoff — 2026-06-05 (proof-ISA COUNT series: both named bounds proven ∅-axiom)

## Branch
`claude/another-challenge-compile-DJWI4` — pushed, ahead of `origin/main`.
`cd lean && lake build E213` ✓ clean.  All new modules strict ∅-axiom
(`tools/scan_axioms.py`): Sperner 47/47, SpernerChains 49/49, Permutations 21/21,
RamseyNamedBound 13/13 — **130 declarations, 0 DIRTY**.

## What Was Done This Session

Compiled two hard problems down the proof-ISA (`seed/PROOF_ISA.md`) to the two
faces of the `COUNT` instruction, **closing the entire COUNT series**.

### 1. Sperner's theorem (1928) — fully proven ∅-axiom
`SpernerChains.sperner_theorem`: the largest antichain of `2^[n]` has size exactly
`C(n,⌊n/2⌋)`.  Sperner is `COUNT`'s **double-counting / LYM** face (the *dual* of
the union bound).
- `Sperner.lean` (47/47): `layer_size` (layer = binomial, the READ),
  `eq_of_subseteq_card_eq` (SEPARATE), `lower_bound` (tight existence),
  `binom_le_binom_mid` (unimodality via the absorption identity `absorb`),
  `lym_double_count`/`sumOver_swap` (the engine = Fubini on a 0/1 matrix),
  `binom_mul_fact`/`fact_mul_ge_mid` (arithmetic), `sperner_upper_bound`
  (abstract reduction: any chain model ⟹ the bound).
- `SpernerChains.lean` (49/49): the geometric chain model — chains =
  `perms (idxList n)`, `inc` = prefix-set; `chain_cap` (`hcap`, nesting) +
  `chain_low` (`hlow`, the `{σ++τ}` injection of `k!(n−k)!` chains).

### 2. The `perms` enumeration — general permutation infrastructure (new to the repo)
`Permutations.lean` (21/21): `perms_length : (perms l).length = l!`,
`mem_perms_iff` (= exactly the rearrangements, via `insert_comm`), `perms_nodup`,
`perms_append_mem` (orderings concatenate).  The repo previously had only `LPerm`
*equivalence*; this is the `n!`-cardinality enumeration, reusable for the Leibniz
determinant.

### 3. Erdős' `R(k,k) > N` named bound — fully proven ∅-axiom
`RamseyNamedBound.lean` (13/13): `ramsey_lower` — `2·C(N,k) < 2^{C(k,2)}` ⟹ a
2-colouring of `K_N`'s edges with no monochromatic `k`-clique.  The `K_N` edge
model instantiating `erdos_schema`; crux `pairsCount_eq` (#internal edges of `S`
= `C(|S|,2)`, via the Pascal step `binom_succ_2`).  Subset count reused from
Sperner (`kLayer_card = C(N,k)`).  This is `COUNT`'s **union-bound** face.

### 4. Marathon (process / essay / org-audit / purity / ready-to-merge)
- process: 0 sink violations; G200/G205 archived to `archive/proof_isa/`, frontier
  board collapsed to a closure record, promotion logged.
- essay: `theory/essays/proof_isa/counting_as_cardinality.md` — "what is counting,
  in 213?" (the COUNT-arc synthesis).
- org-audit: refreshed 3 stale "honest rung" docstrings (now closed in
  SpernerChains); INDEX counts (essays 56→60); CAPSTONE_INDEX entry.
- purity: 0 sorry/Classical/Mathlib/native_decide; all 130 decls strict ∅-axiom.
- ready-to-merge: 0 layer violations, working tree clean; Phase-7.6 synthesis note
  written.  Verdict READY.

## Current Precision Results
Unchanged this session (pure combinatorics; no physics observable touched).
Physics constants table: `catalogs/physics-constants.md`.

## Open Problems (Priority Order)
The COUNT series is **closed** — no open rungs.  The next seeds (all recorded in
`research-notes/frontiers/count_substrate_synthesis.md`, registered in
`frontiers/INDEX.md`):
### 1. A clean strict-order/pow `Meta/Nat` suite
`Nat.mul_lt_mul_right` carries **Classical.choice**, `Nat.pow_add`/`Nat.succ_sub`
carry propext — re-proven ad-hoc per file (`mul_lt_mul_right_clean`,
`pow_add_clean`, `succ_sub_clean`).  Canonicalise + dedup into `Meta/Nat`.
### 2. More LYM-shaped named bounds on the same substrate
Dilworth/Mirsky (chain/antichain duality), Bollobás' set-pair inequality, the
explicit fractional LYM `Σ 1/C(n,|A|) ≤ 1` — all reuse `lym_double_count` +
`perms`/`kLayer`.
### 3. Leibniz determinant over `perms`
`Linalg213/Permutation` uses `LPerm` equivalence + inversion-sign but no
enumeration; `perms` + `mem_perms_iff` + `perms_nodup` now supply the index set
for `det = Σ_{σ∈perms} sign(σ)·Π M i σ(i)`.

## Unresolved from This Session
None — both targets (Sperner, named Ramsey) closed end-to-end.  Note for the next
propext/Classical hunt: core `Nat.mul_lt_mul_right` pulls `Classical.choice`,
`Nat.{mul_assoc,mul_left_comm,add_mul,div_add_mod,succ_sub,pow_add}` and
`List.length_map` pull propext — use NatHelper / `Binomial.add_mul_pure` /
`List213` / structural `half`; `==` on `Nat` is `instBEqOfDecidableEq` (use
`Nat.beq`); `funext` pulls `Quot.sound` (use `*_congr`).

## Next
Merge to `main`.  Then: the `Meta/Nat` clean-arithmetic suite (Open Problem 1, the
recurring tax), or a different domain (primacy = breadth).

## Three-tier state
- **Promotions this session**: `theory/essays/proof_isa/{sperner_double_counting,
  counting_as_cardinality}.md`; G200/G205 source notes archived to
  `research-notes/archive/proof_isa/`.
- **Promotion candidates**: none outstanding for this arc (essays cover it).
- **Active scratchpad**: `research-notes/frontiers/count_substrate_synthesis.md`
  (the post-closure seeds).

## File Map
```
lean/E213/Lib/Math/Combinatorics/Sperner.lean        ← LYM engine + arithmetic + reduction (47/47)
lean/E213/Lib/Math/Combinatorics/Permutations.lean   ← full perms characterisation (21/21)
lean/E213/Lib/Math/Combinatorics/SpernerChains.lean  ← chain model + sperner_theorem (49/49)
lean/E213/Lib/Math/Combinatorics/RamseyNamedBound.lean ← K_N edge model + ramsey_lower (13/13)
lean/E213/Lib/Math/Combinatorics.lean / INDEX.md     ← umbrella + module table (all registered)
theory/essays/proof_isa/sperner_double_counting.md   ← Sperner = dual union bound (the "why")
theory/essays/proof_isa/counting_as_cardinality.md   ← COUNT-arc synthesis essay
theory/essays/proof_isa/probabilistic_method.md      ← Ramsey named bound closed (updated)
research-notes/archive/proof_isa/G200,G205*.md        ← archived (series closed)
research-notes/frontiers/count_substrate_synthesis.md ← post-closure seeds
STRICT_ZERO_AXIOM.md / CAPSTONE_INDEX.md             ← closures registered
```
