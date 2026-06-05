# Session Handoff — 2026-06-05 (Sperner's theorem compiled to the proof-ISA)

## Branch
`claude/another-challenge-compile-DJWI4` — commits pushed ahead of `origin`.
`cd lean && lake build E213` ✓ clean (307/307).  `tools/scan_axioms.py
E213.Lib.Math.Combinatorics.Sperner` → **39/39 PURE / 0 DIRTY**.

## What was done this session

Compiled **Sperner's theorem** (1928 — the largest antichain in the Boolean
lattice `2^[n]` has size `C(n,⌊n/2⌋)`) down the proof-ISA (`seed/PROOF_ISA.md`),
into the **double-counting / dual-union-bound** face of the `COUNT` instruction
— the mirror of the probabilistic-method union bound (G200).  New file
`lean/E213/Lib/Math/Combinatorics/Sperner.lean`, **all strict ∅-axiom**:

### Closed, general (∅-axiom)
- **`layer_size`** — `#{A ⊆ [n] : |A| = k} = binom n k`.  The count-Lens READ;
  the count recursion *is* Pascal's recursion.
- **`eq_of_subseteq_card_eq`** — equal-size distinct sets are incomparable
  (SEPARATE; the inclusion order splits a layer to its diagonal).
- **`lower_bound`** — the middle layer is an antichain of size `binom n ⌊n/2⌋`
  (tight existence half).
- **Binomial unimodality** — `binom_le_binom_mid : binom n k ≤ binom n ⌊n/2⌋`,
  via the absorption identity `absorb : (k+1)·C(n,k+1) = (n−k)·C(n,k)` +
  `binom_mono_up/down` + `binom_climb_up/down` (descends from `⌊n/2⌋` with the
  weak `n ≤ 2k+1` condition — *no symmetry lemma needed*).  Structural `half`
  (= ⌊n/2⌋) avoids the propext-tainted `Nat.div` lemmas.
- **`uniform_antichain_le`** — Sperner for single-size antichains, fully general.
- **`lym_double_count`** — the LYM inequality engine = the dual union bound:
  `sumOver_swap` (Fubini on a 0/1 incidence matrix) + each chain meeting the
  antichain ≤ once ⟹ `Σ chains-through(A) ≤ #chains`.
- **`sperner_numbers`** — `C(n,⌊n/2⌋) = 1,2,3,6,10,20` for `n=1..6`.

### Purity-engineering notes (for the next propext hunt)
`==` on `Nat` is `instBEqOfDecidableEq` (won't reduce on `succ`, propext-risky)
→ used `Nat.beq` directly.  propext-carriers swapped for clean equivalents:
`Nat.add_mul`→`Binomial.add_mul_pure`; `Nat.add_sub_cancel'`→`NatHelper.add_sub_of_le`;
`Nat.le_sub_of_add_le`→`NatHelper.le_sub_of_add_le`; `Nat.sub_le_of_le_add`→
`Nat.sub_le_sub_right`+`add_sub_cancel_right`; `Nat.div_add_mod`→ structural
`half`.  `omega213` only proves `≤`/`<` goals (not equalities) — do arithmetic
equalities by hand.  `funext` pulls `Quot.sound` — use `bcount_congr`/`sumOver_congr`.

## Open Problems (priority order)

### 1. The shared named-bound rung — a permutation enumeration `allPerms n`
Both the named Sperner upper bound (chain-counts `n!`, `k!(n−k)!`) and the named
Ramsey `R(k,k) > 2^{k/2}` (event count `t = C(N,k)`) reduce to **one** missing
piece: a permutation enumeration `allPerms n` with `length = n!` (the repo has
`LPerm` *equivalence*, `Linalg213/Permutation.lean`, but no `n!`-length
enumeration), plus the `k!(n−k)!` prefix-set count.  Building it closes *both*
named bounds.  Pure `Nat`/list bookkeeping, no new "why".  Frontier:
`research-notes/frontiers/G205_sperner_double_count_compilation.md`.

### 2. The factorial identity `binom n k · (k!·(n−k)!) = n!`
Clean ∅-axiom induction; the bridge from `lym_double_count` (`Σ |A|!(n−|A|)! ≤
n!`) to the LYM fractional form.  Unbuilt; reachable.

## Next
- Push commits.  Then: build `allPerms n` (Open Problem 1) to close both named
  bounds, or move to a different domain (primacy = breadth).

## Three-tier state
- **Promotion this session**: `theory/essays/proof_isa/sperner_double_counting.md`
  (the "why" — Sperner as the union bound's dual; the number as READ ∘
  unimodality; the honest rung).
- **Active scratchpad**: `research-notes/frontiers/G205_sperner_double_count_compilation.md`.

## File Map
```
lean/E213/Lib/Math/Combinatorics/Sperner.lean        ← the compilation (39/39 PURE)
lean/E213/Lib/Math/Combinatorics.lean                ← umbrella (Sperner registered)
lean/E213/Lib/Math/Combinatorics/INDEX.md            ← module + proof-ISA entries
theory/essays/proof_isa/sperner_double_counting.md   ← the "why" essay
theory/essays/proof_isa/INDEX.md                     ← series now 5 techniques (4 close)
research-notes/frontiers/G205_*.md                   ← the shared permutation-enum rung
research-notes/frontiers/INDEX.md                    ← two named rungs, one shared gap
STRICT_ZERO_AXIOM.md                                 ← Sperner 39/39 PURE addition (2026-06-05)
```
