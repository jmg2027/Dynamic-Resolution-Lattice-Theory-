# Session Handoff — 2026-06-05 (LYM inequality: the per-term refinement Sperner discards)

## Branch
`claude/substrate-synthesis-count-zq9K0` — pushed.
`cd lean && lake build E213.Lib.Math.Combinatorics` ✓ clean.  New module strict
∅-axiom (`tools/scan_axioms.py`): **LymInequality 5/5 PURE, 0 DIRTY**.

## What Was Done This Session

Harvested the first seed of `research-notes/frontiers/count_substrate_synthesis.md`
("explicit fractional LYM `Σ 1/C(n,|A|) ≤ 1` for free"): stated and closed the
**LYM (Lubell–Yamamoto–Meshalkin / Bollobás–LYM) inequality** as its own named
theorem — the per-term refinement the Sperner development discarded.

### `LymInequality.lean` (5/5 PURE) — new module
The existing Sperner closure ran *through* `Sperner.lym_double_count` but
immediately collapsed each summand to its minimum (`fact_mul_ge_mid`) before
reading off `|F| ≤ C(n,⌊n/2⌋)`.  LYM is that engine **stopped one line earlier**:
- `lym_inequality` — engine form: over any chain model (`#chains = n!`, ≤ 1
  member per chain `hcap`, ≥ `|A|!(n−|A|)!` chains per member `hlow`),
  `Σ_{A∈F} |A|!·(n−|A|)! ≤ n!`.  ~3 lines from `lym_double_count` + `sumOver_le`.
- ★★ `lym_antichain` — named, unconditional: every antichain of `2^[n]` satisfies
  `Σ_{A∈F} |A|!·(n−|A|)! ≤ n!`.  This is `Σ 1/C(n,|A|) ≤ 1` cleared of
  denominators (`binom_mul_fact`: `C(n,k)·k!·(n−k)! = n!`).  Instantiates the
  engine over the `SpernerChains` model (`chains_length`, `chain_cap`, `chain_low`).
- `lym_tight_layer` — **sharpness / equality case**: a full layer `kLayer n k`
  (`k ≤ n`) saturates LYM at `= n!` (every term `k!·(n−k)!`, `C(n,k)` of them).
  So the layers are exactly the extremal antichains.
- `sperner_via_lym` — **LYM ⟹ Sperner**: re-derives `|F| ≤ C(n,⌊n/2⌋)` *from* the
  named inequality (apply the discarded `min`, then cancel), making "Sperner ⊂
  LYM" a fact in the Lean.
- `lym_tight_examples` — saturation at `(n,k) = (3,1)` and `(4,2)`.

No new counting infrastructure was needed — the engine (`lym_double_count`,
`sumOver_swap`), the arithmetic (`binom_mul_fact`, `fact_mul_ge_mid`), and the
chain model (`chain_cap`, `chain_low`) all pre-existed.  The content is *where
the compilation stops*: a theorem and its famous corollary differ by one `min`.

### Marathon (essay / INDEX / catalog)
- essay: `theory/essays/proof_isa/lym_inequality.md` — "the per-term refinement
  Sperner throws away"; the compiled form shows LYM and Sperner share every
  instruction but the last (`min`).
- INDEX: `Combinatorics/INDEX.md` (LymInequality row), `theory/essays/INDEX.md`
  + `theory/essays/proof_isa/INDEX.md` (essay entries), `STRICT_ZERO_AXIOM.md`
  (5/5 PURE entry), `Combinatorics.lean` umbrella import.
- frontier: `count_substrate_synthesis.md` — fractional-LYM seed marked ✓ closed.

## Current Precision Results
Unchanged this session (pure combinatorics; no physics observable touched).
Physics constants table: `catalogs/physics-constants.md`.

## Open Problems (Priority Order)
From `research-notes/frontiers/count_substrate_synthesis.md` (registered in
`frontiers/INDEX.md`):
### 1. More LYM-shaped named bounds on the same substrate
**Dilworth/Mirsky** (chain/antichain duality) and **Bollobás' set-pair
inequality** remain open.  Bollobás: orderings with "all of `A` before all of
`B`", events disjoint by cross-intersection (`A_i∩B_j ≠ ∅`); the remaining infra
is the exact ordering count `#E_i·(a+b)! = n!·a!·b!`.  Both reuse `perms`/`kLayer`.
### 2. A clean strict-order/pow `Meta/Nat` suite
`Nat.mul_lt_mul_right` carries **Classical.choice**; `Nat.pow_add`/`Nat.succ_sub`
carry propext — re-proven ad-hoc per file.  Canonicalise into `Meta/Nat`.
### 3. Leibniz determinant over `perms`
`Linalg213/Permutation` has `LPerm` equivalence + inversion-sign but no
enumeration; `perms` + `mem_perms_iff` + `perms_nodup` supply the index set for
`det = Σ_{σ∈perms} sign(σ)·Π M i σ(i)`.

## Next
Merge to `main`, or continue the COUNT substrate (Bollobás set-pair, the natural
next LYM-shaped named bound), or a different domain (primacy = breadth).

## File Map
```
lean/E213/Lib/Math/Combinatorics/LymInequality.lean  ← LYM named inequality (5/5 PURE)  [NEW]
lean/E213/Lib/Math/Combinatorics/Sperner.lean        ← lym_double_count engine + fact_mul_ge_mid (the discarded min)
lean/E213/Lib/Math/Combinatorics/SpernerChains.lean  ← chain model (chains_length, chain_cap, chain_low)
lean/E213/Lib/Math/Combinatorics.lean / INDEX.md     ← umbrella + module table (LymInequality registered)
theory/essays/proof_isa/lym_inequality.md            ← LYM = Sperner's engine stopped before the min  [NEW]
theory/essays/{INDEX,proof_isa/INDEX}.md             ← essay entries
research-notes/frontiers/count_substrate_synthesis.md ← fractional-LYM seed marked closed
STRICT_ZERO_AXIOM.md                                  ← 5/5 PURE closure registered
```
