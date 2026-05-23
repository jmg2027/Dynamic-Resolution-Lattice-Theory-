# Cardinality cut-off principle — applications

Concrete realisations of the cardinality cut-off principle
(`cardinality_cutoff_principle.md`) across six directions.  Each
direction instantiates the three-step methodology (locate /
diagnose / refined-prove, §5 of principle) for a different
`(f, H_k)` pair or different DRLT primitive set.

Aggregate: 191 PURE / 0 DIRTY across six Lean files in
`lean/E213/Lib/Math/Cohomology/Fractal/`.

## §1 Overview

The cardinality cut-off principle is parametric in three slots:

  · External sequence `f : ℕ → ℕ` (Aurifeuillean L-coefficient,
    Pell number, etc.).
  · DRLT complexity class `H_k ⊆ ℕ` (depth-bounded Hunter values).
  · Primitive set generating `H_k` (canonical `{2, 3, 5}` or
    alternates).

The six directions explore different fillings of these slots:

| Direction | Slot exercised | Concrete instance |
|---|---|---|
| B | premise (`f → ∞`) | Aurifeuillean L_m chain m ∈ {1, 3, 7} |
| D | catalogue closure | Hunter atomic primes under mod-p ops |
| A | depth-k extension | depth-2 restricted (outer ∈ {+, *}) |
| C | sequence reusability | Pell numbers as external sequence |
| E | complexity measure | hunterComplexity(v) hierarchy |
| F | primitive parametricity | {2, 3} alternate (drop d = 5) |

## §2 Direction B — Aurifeuillean L unboundedness

Closes the verbal premise "L_m → ∞" of the principle's §3 via a
concrete finite chain at squarefree odd m coprime to 10.

**Chain** (computed externally via PARI/GP `bnfisnorm` over
`K = Q(√5)`):

| m | L_m | M_m | Φ_{10m²}(5) |
|---|---|---|---|
| 1 | 29 | 8 | 521 |
| 3 | 850 554 441 | 364 242 064 | 60 081 451 169 922 001 |
| 7 | ≈ 5.27 × 10⁵⁸ (59 digits) | ≈ 4.67 × 10⁵⁷ (58 digits) | ≈ 2.67 × 10¹¹⁷ (118 digits) |

**Norm identity** `L_m² − 5·M_m² = Φ_{10m²}(5)` decide-verified at
each m.  Cap `= L_7` covers any plausible Hunter depth-k bound for
small k (M_1 = 3125, M_{2,r} = 9 765 625 — both ≪ L_7).

**Lean**: `AurifeuilleanLUnbounded.lean` (20 PURE).  Main theorem:

```
L_bounded_unboundedness :
  ∀ B : Nat, B < Lval 7 → ∃ m : Nat, B < Lval m
```

Case split on `B < 29` (m=1), `B < 850 554 441` (m=3), else m=7.

## §3 Direction D — Hunter atomic prime catalogue closure

Tests whether the catalogue `{2, 3, 5, 7, 13, 41, 137, 521}` is
closed under `(a op b) % p` for op ∈ {+, *, ^}, p ∈ catalogue.

**Verdict**: catalogue is **not** closed under any operation.
Closure counts per op per modulus (out of 64 ordered pairs):

| p | + | × | ^ |
|---|--:|--:|--:|
| 2 | 0 | 0 | 0 |
| 3 | 14 | 20 | 35 |
| 5 | 26 | 20 | 35 |
| 7 | 31 | 23 | 27 |
| 13 | 25 | 14 | 13 |
| 41 | 16 | 3 | 16 |
| 137 | 16 | 4 | 10 |
| 521 | 18 | 1 | 9 |

**Sub-closure**: catalogue contains a 28-pair **FLT sub-closure**
`{(a, p) : a, p ∈ cat, a < p}`.  For each such pair, Fermat's
Little Theorem gives `a^p ≡ a (mod p)`, hence `powMod a p p = a ∈ cat`.

Pair count: `0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 = 28`.

**Lean**: `HunterAtomicClosure.lean` (54 PURE).  `powMod`-based
implementation avoids kernel exponentiation-threshold limits;
needs `set_option maxRecDepth 16384` for the `closure_pow_521`
decide.

## §4 Direction A — Restricted depth-2 cut-off

Extends `cutoff_marathon_at_depth_1` from depth 1 (M_1 = 3125) to
a restricted depth 2.  Trees `(a opL b) opOut (c opR d)` with
**outer op ∈ {+, *}** (no outer ^).

Restriction rationale: unrestricted depth-2 includes
`pow gd (pow gd gd) = 5^3125` (~2184 digits), exceeding Lean
kernel exponentiation threshold (256).  Restricting `opOut` bounds
the maximum at `3125 · 3125 = 9 765 625`, kernel-feasible.

**Cut-off**: `∀ v > 9 765 625`, `v` is not the value of any
restricted-depth-2 Hunter expression.  Applies to L_3, L_7, and
all Aurifeuillean L_m for m ≥ 3.

**Lean**: `AurifeuilleanDepth2Cutoff.lean` (12 PURE).  Bound proved
by decide over 1458 = 3⁴ × 3² × 2 parameter combinations.

**Open frontier**: outer = ^ case via algebraic prime-factorisation
argument (137, 521 prime + not in depth-1 → not in depth-2-pow).

## §5 Direction C — Pell sequence cut-off

Applies the principle to a **non-Aurifeuillean** external sequence:
Pell numbers `P_n` with `P_{n+2} = 2P_{n+1} + P_n`.

| n | P_n |
|---|---:|
| 5 | 29 |
| 10 | 2 378 |
| 11 | 5 741 |
| 19 | 6 625 109 |
| 20 | 15 994 428 |

**Pell–Aurifeuillean coincidence**: `P_5 = 29 = L_1`.  Two
a-priori-unrelated external sequences both meet the Aurifeuillean
L-coefficient at small index.  29 has three Hunter readings
(NT^d − NS, d² + NT², d² + d − 1) — a triple-encoded constant in
the catalogue.

**Cut-off slices**:

  · Depth 1 (M_1 = 3125): P_n ∉ H_1 for n ≥ 11 (sharp boundary:
    P_10 = 2378 < 3125 < 5741 = P_11).
  · Restricted depth 2 (M_{2,r} = 9 765 625): P_n ∉ H_{2,r} for
    n ≥ 20 (boundary: P_19 < M_{2,r} < P_20).

**213-internal motivation**: Pell connects to the dyadic FSM /
Pisano period analysis (`theory/math/dyadic_fsm.md`), making this
a natural 213-internal test case rather than an arbitrary external
choice.

**Lean**: `PellCutoff.lean` (35 PURE).  Recurrence-defined `Pell : Nat → Nat`
+ 21 explicit values + cut-off applications.

## §6 Direction E — Hunter complexity measure

Defines `hunterComplexity(v)` = minimum depth `k` such that `v`
admits a Hunter expression of depth ≤ `k`.

**Hierarchy** (with catalogue atom representatives):

| complexity | universe size | atoms |
|---|---|---|
| 0 | 3 (= generators) | 2, 3, 5 |
| 1 | 16 distinct values | 4, 6, 7, 8, 9, 10, 15, 25, 27, 32, 125, 243, 3125 |
| 2 | larger | 13, 29, 41 |
| 3 | larger | 137, 521 |

**Complexity table for catalogue atoms**:

| atom | complexity | witness                              |
|------|-----------|--------------------------------------|
| 2    | 0         | gNT                                  |
| 3    | 0         | gNS                                  |
| 5    | 0         | gd                                   |
| 7    | 1         | `2 + 5`                              |
| 13   | 2         | `(2^3) + 5`                          |
| 41   | 2         | `(3^2) + (2^5) = 9 + 32`             |
| 137  | 3         | `(2^(2+5)) + (3^2) = 128 + 9`        |
| 521  | 3         | `(2^(3^2)) + (3^2) = 512 + 9`        |

Depth-3 lower bound for {137, 521} is restricted to outer ∈ {+, *}
(depth-2 outer pow argument requires prime-not-in-depth-1, deferred).

**Lean**: `HunterComplexity.lean` (39 PURE).  Explicit `depth1Universe`
list (16 values) + soundness/completeness + complexity-hierarchy
capstone.

## §7 Direction F — Alternate primitive set

Drops `d = 5` from `{2, 3, 5}`, leaving the two-generator alternate
`{NT, NS} = {2, 3}`.

**Universe comparison**:

| set | depth-1 max | depth-1 distinct values |
|---|---|---|
| `{2, 3, 5}` (canonical) | 3125 | 16 |
| `{2, 3}` (alt, no d) | 27 | 8 |

**Catalogue mobility** (complexity in alt set vs canonical):

| atom | canonical | alt    |
|------|-----------|--------|
| 2    | 0         | 0      |
| 3    | 0         | 0      |
| 5    | 0         | 1 (= 2 + 3) |
| 7    | 1         | ≥ 2    |
| 13   | 2         | ≥ 3    |
| 41   | 2         | 2 (= 3² + 2⁵ — uses only {2, 3}) |
| 137  | 3         | ≥ 3    |
| 521  | 3         | ≥ 3    |

**Lean**: `AltPrimitiveSet.lean` (31 PURE).  Demonstrates the cut-off
principle's structural content is independent of primitive choice;
the cut-off slice moves with the set.

## §8 Cross-cutting structural findings

  1. **Two external sequences coincide at the smallest index**:
     `P_5 = L_1 = 29`.  29 is triple-encoded in the Hunter
     catalogue (`d² + NT² = NT^d − NS = d² + d − 1`).  The
     coincidence is the principle's "locate" step instantiated
     across two unrelated sequences.

  2. **Catalogue carries an FLT sub-closure**: under mod-p ops,
     `{(a, p) ∈ cat² : a < p}` is closed via `a^p ≡ a (mod p)`.
     28 pairs.  No general closure beyond this.

  3. **Hunter complexity is honest at 4 levels** for catalogue
     atoms, with concrete witnesses at each level.  Depth-1
     universe has exactly 16 distinct values.

  4. **Principle parametric in primitive set**: changing the
     primitive generators preserves methodology but shifts the
     complexity assignment of catalogue atoms (most dramatically:
     `5` moves from depth 0 to depth 1 when `d` is dropped).

## §9 Direction A unrestricted — depth-2 outer-pow case CLOSED

The previously-open outer-pow frontier of Direction A is closed
via a kernel-feasible enumeration + monotonicity split.

**Strategy** (`AurifeuilleanDepth2PowCutoff.lean`, 18 PURE):

  · **Small range** `b ∈ {2, …, 10}` (9 values, all `< 256`
    kernel exponentiation threshold): 16 × 9 = 144 pairs
    `(a, b)`, each `a^b ≤ 3125^10 ≈ 10^35`, decide-checked.

  · **Large range** `b ∈ {15, 25, 27, 32, 125, 243, 3125}`
    (7 values): monotonicity argument
    `a ≥ 2 ∧ b ≥ 15 → a^b ≥ 2^15 = 32768 > 521 > 137`, via
    `Nat.pow_le_pow_{left,right}`.

  · **Dispatch**: split on `j.val < 9` (small) or `j.val ≥ 9`
    (large); the 16-element depth-1 universe partitions
    cleanly into the two ranges with no overlap.

**Combined verdict for catalogue primes `{137, 521}`**:

  · restricted depth-2 (outer ∈ {+, *}): covered by
    `HunterComplexity.complexity_{137,521}_at_least_3_restricted`.
  · outer-pow case: covered by `AurifeuilleanDepth2PowCutoff.depth2_pow_ne_{137,521}`.

Hence `hunterComplexity(137) = 3` and `hunterComplexity(521) = 3`
**without** the "restricted to outer ∈ {+, *}" qualifier.  The
upper bound (= 3) follows from the explicit depth-3 witnesses
`2^(2+5) + 3^2` and `2^(3^2) + 3^2`.

## §10 Remaining frontier

  · **Direction B continuation**: extend Aurifeuillean L_m chain
    to m = 11.  Φ_{1210}(5) is 308 digits; PARI/GP `bnfisnorm`
    class-group cost grows with index.

  · **Direction C extensions**: apply principle to additional
    external sequences (Lucas, Fermat, cyclotomic at bases
    other than 5).  Each gives a `(f, H_k)` instance with
    different growth rates and coincidence patterns.

  · **Direction E**: extend `hunterComplexity` to a full Lean
    function with bounded search; structural complexity-hierarchy
    theorem `{v : hunterComplexity(v) ≤ k}` properly chains in k.

  · **Other catalogue atoms at depth-2-pow**: same enumeration +
    monotonicity strategy applies to `13`, `29`, `41` (already
    handled at restricted depth-2); the outer-pow case for these
    is a straightforward extension.

## §11 Cross-references

  · `cardinality_cutoff_principle.md` — methodology chapter.
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanFullCutoff.lean`
    — depth-1 cut-off substrate (28 PURE, predecessor).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanLUnbounded.lean`
    — Direction B (20 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/HunterAtomicClosure.lean`
    — Direction D (54 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanDepth2Cutoff.lean`
    — Direction A restricted (12 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanDepth2PowCutoff.lean`
    — Direction A unrestricted, outer-pow case (18 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/PellCutoff.lean`
    — Direction C (35 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/HunterComplexity.lean`
    — Direction E (39 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AltPrimitiveSet.lean`
    — Direction F (31 PURE).
  · `theory/math/cohomology/aurifeuillean.md` — Aurifeuillean
    cyclotomic context.
  · `theory/math/dyadic_fsm.md` — Pell ↔ dyadic FSM connection.
  · `catalogs/atomic-integers.md` — Hunter atomic primes.
