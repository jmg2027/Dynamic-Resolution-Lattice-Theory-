# Session Handoff — 2026-06-05 (LYM inequality + Bollobás set-pair, on the COUNT substrate)

## Branch
`claude/substrate-synthesis-count-zq9K0` — pushed.
`cd lean && lake build E213.Lib.Math.Combinatorics` ✓ clean.  Two new modules
strict ∅-axiom (`tools/scan_axioms.py`): **LymInequality 5/5 PURE**,
**BollobasSetPair 18/18 PURE**, 0 DIRTY.

## What Was Done This Session (two seeds of count_substrate_synthesis.md)

### Part B — Bollobás' set-pair inequality (`BollobasSetPair.lean`, 18/18 PURE)
The next LYM-shaped named bound: `m ≤ C(a+b,a)` (n-independent) for a
cross-intersecting, per-pair-disjoint family of set pairs.  Same `COUNT`
double-count engine as LYM, a *different incidence* (pairs × orderings, entry =
"ordering favours the pair = all A before all B").
- **New content (the heart)**: `before` (ordering relation) + `before_antisymm`
  (antisymmetry, no `Nodup`), `favours`/`favours_before`, and ★ `bollobas_cap`
  — cross-intersection ⟹ each ordering favours ≤ 1 pair (the column cap; the
  contradiction is `before c x y` ∧ `before c y x` ⟹ `x = y ∈ A_i∩B_i = ∅`).
- ★ `bollobas_sum` — the engine, unconditional: `Σ_i #{favouring i} ≤ n!`
  (= `lym_double_count` on the favour-incidence, verbatim).
- ★★ `bollobas` — the named bound `|F| ≤ C(a+b,a)`, **modulo the favour-count**
  `V·(a+b)! = n!·a!·b!` (the honest open rung — the ordering-count analogue of
  `chain_low`; recorded in the frontier).  Cancellation via `binom_mul_fact`.
Bollobás = LYM's compilation with the incidence swapped and the antichain cap
swapped for the cross-intersection cap — no new engine.  The Bollobás section
was added to `theory/essays/proof_isa/lym_inequality.md`.

### Part A — the LYM inequality (`LymInequality.lean`, 5/5 PURE)

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
### 1. Discharge the Bollobás favour-count rung (closes `bollobas` unconditionally)
The one remaining count: `#{π : all A before all B} = C(n,a+b)·a!·b!·(n−a−b)!`,
i.e. `V·(a+b)! = n!·a!·b!`.  Ordering-count analogue of `SpernerChains.chain_low`:
inject orderings favouring `(A,B)` — choose the `a+b` positions hosting `A∪B`
(`C(n,a+b)`), order `A` into the first `a`, `B` into the next `b` (`a!·b!`),
order the rest (`(n−a−b)!`), via `perms`/`perms_append_mem`.  Feeds `bollobas`'s
`hV`+`hcount` to make `m ≤ C(a+b,a)` unconditional.
### 2. More LYM-shaped named bounds: Dilworth/Mirsky (chain/antichain duality).
### 2. A clean strict-order/pow `Meta/Nat` suite
`Nat.mul_lt_mul_right` carries **Classical.choice**; `Nat.pow_add`/`Nat.succ_sub`
carry propext — re-proven ad-hoc per file.  Canonicalise into `Meta/Nat`.
### 3. Leibniz determinant over `perms`
`Linalg213/Permutation` has `LPerm` equivalence + inversion-sign but no
enumeration; `perms` + `mem_perms_iff` + `perms_nodup` supply the index set for
`det = Σ_{σ∈perms} sign(σ)·Π M i σ(i)`.

## Next
Discharge the Bollobás favour-count rung (Open Problem 1 — closes `bollobas`
unconditionally), then merge to `main`; or a different domain (primacy = breadth).

## File Map
```
lean/E213/Lib/Math/Combinatorics/BollobasSetPair.lean ← Bollobás: before_antisymm, bollobas_cap, bollobas_sum, bollobas (18/18 PURE)  [NEW]
lean/E213/Lib/Math/Combinatorics/LymInequality.lean  ← LYM named inequality (5/5 PURE)  [NEW]
lean/E213/Lib/Math/Combinatorics/Sperner.lean        ← lym_double_count engine + binom_mul_fact + fact_mul_ge_mid
lean/E213/Lib/Math/Combinatorics/SpernerChains.lean  ← chain model (chains_length, chain_cap, chain_low, truePos, idxList, perms)
lean/E213/Lib/Math/Combinatorics.lean / INDEX.md     ← umbrella + module table (both new modules registered)
theory/essays/proof_isa/lym_inequality.md            ← LYM (Sperner's engine before the min) + Bollobás section  [NEW]
theory/essays/{INDEX,proof_isa/INDEX}.md             ← essay entries
research-notes/frontiers/count_substrate_synthesis.md ← fractional-LYM closed; Bollobás heart closed, count rung recorded
STRICT_ZERO_AXIOM.md                                  ← 5/5 + 18/18 PURE closures registered
```
