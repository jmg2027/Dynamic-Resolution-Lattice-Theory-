# Session Handoff — 2026-06-04

## Branch
`claude/eisenstein-elliptic-conjecture-Vvzcx` — pushed, ahead by 4 commits (this marathon).
`cd lean && rm -rf .lake/build && lake build` ✓ (full fresh build clean).  Kernel regress
45/45 0-axiom.  All new modules strict ∅-axiom (`does not depend on any axioms`).

## What Was Done This Session

This branch closed a sequence of classical representation theorems ∅-axiom, capped by Lagrange's
four-square theorem, then ran a full merge-readiness marathon (`/process /essay /org-audit
/purity-check /ready-to-merge /handoff`) and merged `origin/main` in.

**Merged from main this pass** (separate arc, promoted to permanent tiers — see
`research-notes/frontiers/INDEX.md` + `theory/essays/`): the residue-expression atlas + the
Minkowski-`?` modular cocycle (`theory/essays/analysis/minkowski_as_modular_cocycle.md`), the
breadth-signature thesis (`theory/essays/foundations/the_breadth_signature.md`), the Markov-`H`
ISA-localization terminal finding (`frontiers/markov_lagrange/G197…`), and the p-adic
Teichmüller G123 A/B/G closure (`theory/math/numbersystems/padic_real213.md`).

### 1. Lagrange's four-square theorem — CLOSED + PROMOTED (∅-axiom)
`NumberTheory/FourSquare.nat_isSum4 : ∀ n, isSum4 ↑n` is axiom-free — the first repo result
reached by neither the multiplicative counting-bound nor the commutative CD machinery (35 PURE /
0 dirty).  An **additive** pigeonhole seed + an **all-`n`** Euler descent over `ℤ`:
- `FourSquareSeed.four_square_seed` (Pillar I, constructive): odd prime `p = 2m+1` ⟹
  `∃ x y ≤ m, p ∣ x²+y²+1`, via `Pigeonhole.no_inj_lt` on a sum-collision (`gval`); witness from
  a bounded 2-D search refuted in its `none`-branch.  Dodges two propext traps (`a%p` instead of
  `Decidable (p∣a)`; ℕ-only to avoid the `Int.natAbs` triangle).
- `FourSquare`: `four_sq_id` (Euler's identity), `isSum4_mul`, `descent_core`; the **parity-split
  descent** — `halve_step` (even `m` halves) + `odd_descent` (odd `m` strict `r<m`, killing the
  `r=m` mod-8 crux) + `descent_rec` (fuel recursion); `seed_multiple` (`k·p = x²+y²+1²+0²`,
  `1≤k<p`); `dvd_dec`/`searchDiv`/`exists_prime_factor` (constructive least-divisor prime
  factorization); `prime_isSum4`; `nat_isSum4`.  Two more propext leaks caught (`Nat.dvd_refl`,
  `Nat.succ_ne_zero`) → `⟨1,(mul_one _).symm⟩` and `Nat.noConfusion`.
- Promoted: `theory/essays/synthesis/four_square_additive_pigeonhole.md` (the two-engine
  contrast); frontier note archived to `research-notes/archive/four_square/`.

### 2. Earlier on this branch (closed ∅-axiom, carried into the merge)
- **Eisenstein split-converse iff** — `EisensteinConverse.eisenstein_iff`: prime `p ≠ 3`,
  `p ≡ 1 (mod 3) ⟺ ∃ a b, ↑p = a²−ab+b²`.  Pillar I (Lagrange root bound mod `p` via `PolyRoot`)
  + ℤ[ω] norm-Euclidean descent.  Promoted: `theory/math/numbertheory/eisenstein_period_arithmetic.md`.
- **Gaussian two-square iff** — `GaussianTwoSquare.two_square_iff`: odd prime, `p ≡ 1 (mod 4) ⟺
  p = a²+b²`.
- **Parametric ℤ[√−D]** — `ZSqrtNegSplit.split_form` (`1≤D≤2`, `p∣x²+D ⟹ p = a²+D·b²`); the
  `D=2` (disc-`−8`) conditional split.
- **Sharpness (negative result)** — `ZSqrtNegSharp.descent_false_at_three`: the descent bound
  `D≤2` is optimal (`2 ∣ 1²+3` yet `2 ≠ a²+3b²`).
- Synthesis essay: `theory/essays/synthesis/representation_theorems_one_counting_bound.md`.

### 3. Marathon hygiene (this pass)
- **process**: decoupled the FourSquare docstring from its frontier note (sink rule: 0 violations).
- **org-audit**: refreshed `theory/INDEX` + `theory/essays/INDEX` counts (essays 41→44, math
  87→88, ~176 total); narrative + stale-ref clean.
- **ODE build fix**: `Analysis/ODE.lean` had imports after the docstring (Lean-invalid, masked by
  olean cache) — hoisted them; `E213.Lib.Math` aggregator now builds.
- **ready-to-merge synthesis**: `research-notes/frontiers/sums_of_squares_engines.md`.

## Current Precision Results (0 free parameters)
Unchanged this session (math-frontier work only; no physics-constant edits).  Canonical table:
`catalogs/physics-constants.md`.

## Open Problems (Priority Order)

### 1. Disc-`−8` congruence iff
`ZSqrtNegSplit.split_form_two` gives `p ∣ x²+2 ⟹ p = a²+2b²`; the missing forward half is which
primes have `−2` a QR (`p ≡ 1,3 mod 8`), i.e. the quadratic character of `2` — the one input the
multiplicative engine still lacks.  Frontier: `research-notes/frontiers/sums_of_squares_engines.md`.

### 2. Three-square theorem (`n = a²+b²+c²` iff `n ≠ 4ᵏ(8m+7)`)
Outside both representation engines: three squares is not multiplicative, so the prime reduction
does not apply.  Hard / possibly out-of-reach ∅-axiom (classical proof needs Dirichlet + ternary
genus theory).  Frontier: `research-notes/frontiers/sums_of_squares_engines.md`.

### 3. Promotion backlog
Gaussian / ℤ[√−D] / PolyRoot PURE-closed sub-trees still lack `theory/` chapters.  Frontier:
`research-notes/frontiers/research_grade_closure_gate.md` (gate discussion); promote per
`theory/PROMOTION_CRITERIA.md`.

### 4. (carried) Markov uniqueness, π non-holonomicity, spiral-axis, completability
See `research-notes/frontiers/INDEX.md` for the full open board.

## Unresolved from This Session
None attempted-and-failed.  One informational backlog surfaced by `ready-to-merge`: **121
repo-wide namespace mismatches** (`tools/sync_namespaces.py`, e.g. `Lens/Cardinality/Godel`) —
pre-existing drift, not from this branch (its files are namespace-clean).  Deserves a dedicated
`sync_namespaces --apply` commit chain, not a merge-audit fold-in.

## Next
- Disc-`−8` congruence iff: derive the quadratic character of `2` ∅-axiom (Pillar-I residue
  input), then close `p ≡ 1,3 (mod 8) ⟺ p = a²+2b²`.
- Or: clear the namespace-drift backlog (`sync_namespaces --apply`) as its own commit chain.
- Or: promote the Gaussian / ℤ[√−D] / PolyRoot closed sub-trees to `theory/`.

## Three-tier state
- **Promotions this session**: `theory/essays/synthesis/four_square_additive_pigeonhole.md` ←
  `research-notes/frontiers/four_square_marathon.md` (now `archive/four_square/`).
- **Promotion candidates**: Gaussian (`GaussianTwoSquare`), ℤ[√−D] (`ZSqrtNegSplit/Sharp`),
  PolyRoot (`RootBound`/`IntEuclid`/…) — PURE-closed, no `theory/` chapter yet.
- **Active scratchpad**: `research-notes/frontiers/` open board (see its `INDEX.md`).

## File Map
```
lean/E213/Lib/Math/NumberTheory/FourSquare.lean        ← +§5-§7: descent_rec, seed_multiple,
                                                          exists_prime_factor, prime_isSum4,
                                                          nat_isSum4 (35 PURE / 0 dirty)
lean/E213/Lib/Math/Analysis/ODE.lean                   ← imports hoisted above docstring (build fix)
theory/essays/synthesis/four_square_additive_pigeonhole.md  ← NEW essay (four-square promotion)
theory/essays/INDEX.md                                 ← +2 synthesis rows, count 41→44
theory/INDEX.md                                        ← counts essays 44 / math 88 / ~176
research-notes/frontiers/sums_of_squares_engines.md    ← NEW synthesis seed
research-notes/frontiers/INDEX.md                      ← four-square closure record + new seed
research-notes/archive/four_square/four_square_marathon.md  ← archived (was in frontiers/)
research-notes/promotion_essay_log.md                  ← +1 promotion+essay row
```
