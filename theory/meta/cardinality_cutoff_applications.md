# Cardinality cut-off principle — applications

Concrete realisations of the cardinality cut-off principle
(`cardinality_cutoff_principle.md`) across six directions.  Each
direction instantiates the three-step methodology (locate /
diagnose / refined-prove, §5 of principle) for a different
`(f, H_k)` pair or different DRLT primitive set.

Aggregate: 291 PURE / 0 DIRTY across ten Lean files in
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

Tests whether the catalogue `{2, 3, 5, 7, 13, 521}` is closed
under `(a op b) % p` for op ∈ {+, *, ^}, p ∈ catalogue.

**Verdict**: catalogue is **not** closed under any operation.
Closure counts per op per modulus (out of 36 ordered pairs):

| p | + | × | ^ |
|---|--:|--:|--:|
| 2 | 0 | 0 | 0 |
| 3 | 10 | 12 | 15 |
| 5 | 13 | 8 | 20 |
| 7 | 18 | 10 | 16 |
| 13 | 15 | 10 | 8 |
| 521 | 14 | 0 | 5 |

**Sub-closure**: catalogue contains a 15-pair **FLT sub-closure**
`{(a, p) : a, p ∈ cat, a < p}`.  For each such pair, Fermat's
Little Theorem gives `a^p ≡ a (mod p)`, hence `powMod a p p = a ∈ cat`.

Pair count: `0 + 1 + 2 + 3 + 4 + 5 = 15`.

**Lean**: `HunterAtomicClosure.lean` (44 PURE).  `powMod`-based
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

**Open frontier**: outer = ^ case for `521` closed in §9.

## §5 Direction C — Pell, Lucas, Fibonacci, Tribonacci sequence cut-offs

Applies the principle to **four non-Aurifeuillean** external
sequences:

  · Pell (`P_{n+2} = 2P_{n+1} + P_n`)
  · Lucas (`L_{n+2} = L_{n+1} + L_n`)
  · Fibonacci (`F_{n+2} = F_{n+1} + F_n`)
  · Tribonacci (`T_{n+3} = T_{n+2} + T_{n+1} + T_n`)

### Pell

| n | P_n |
|---|---:|
| 5 | 29 |
| 10 | 2 378 |
| 11 | 5 741 |
| 19 | 6 625 109 |
| 20 | 15 994 428 |

Cut-off slices:
  · Depth 1 (`M_1 = 3125`): `n ≥ 11` (boundary `P_10, P_11`).
  · Restricted depth 2 (`M_{2,r} = 9 765 625`): `n ≥ 20`.

213-internal motivation: Pell connects to the dyadic FSM /
Pisano period analysis (`theory/math/dyadic_fsm.md`).

### Lucas

| n  | L_n  | catalogue role             |
|----|------|----------------------------|
| 0  | 2    | NT (generator)             |
| 2  | 3    | NS (generator)             |
| 4  | 7    | catalogue prime            |
| 7  | 29   | catalogue                  |
| 13 | 521  | catalogue prime, `Φ_10(5)` |

Lucas hits the catalogue at **five** indices, more than any other
external sequence considered.

Cut-off slices:
  · Depth 1: `n ≥ 17` (boundary `L_16 = 2207, L_17 = 3571`).
  · Restricted depth 2: `n ≥ 34` (boundary `L_33 = 7 881 196,
    L_34 = 12 752 043`).

### Triple-sequence coincidence at 29

★ **`Pell P_5 = Lucas L_7 = Aurifeuillean L_1 = 29`**.

Three external sequences agree on the smallest depth-2 catalogue
atom.  `29` has three Hunter readings:
  · `NT^d − NS = 2^5 − 3 = 29`
  · `d² + NT² = 25 + 4 = 29`
  · `d² + d − 1 = 25 + 5 − 1 = 29`

The triple-agreement is the principle's "locate" step
instantiated simultaneously across all three sequences at the
same catalogue atom.

### Lucas–Aurifeuillean coincidence at 521

★ **`Lucas L_13 = Φ_10(5) = 521`** (catalogue handle of
`N_U + 1 = 5^(5^n) + 1`, n-uniform).

### Fibonacci

| n | F_n | catalogue role                  |
|---|----|---------------------------------|
| 3 | 2  | NT (generator)                  |
| 4 | 3  | NS (generator)                  |
| 5 | 5  | d (generator)                   |
| 7 | 13 | catalogue prime (`= NS² + NT²`) |

★ **Three Hunter generators in a length-3 Fibonacci window**:
`(F_3, F_4, F_5) = (NT, NS, d) = (2, 3, 5)`.  The entire canonical
Hunter primitive set appears as three consecutive Fibonacci values.
This is the structurally tightest catalogue coincidence in the
applications family.

Cut-off slices:
  · Depth 1: `n ≥ 19` (boundary `F_18 = 2584, F_19 = 4181`).
  · Restricted depth 2: `n ≥ 36` (boundary `F_35 = 9 227 465,
    F_36 = 14 930 352`).

### Tribonacci

| n | T_n | catalogue role  |
|---|----|----------------|
| 4 | 2  | NT             |
| 6 | 7  | catalogue prime |
| 7 | 13 | catalogue prime |

★ **Tightest near-boundary in the family**: `T_16 = 3136` is
exactly `11` above `M_1 = 3125`.  Tribonacci's slower growth rate
(constant ψ ≈ 1.839 vs golden ratio ≈ 1.618 vs Pell-silver ≈ 2.414)
produces this near-miss.

Cut-off slices:
  · Depth 1: `n ≥ 16` (boundary `T_15 = 1705, T_16 = 3136`).
    Tightest in the family.
  · Restricted depth 2: `n ≥ 30` (boundary `T_29 = 8 646 064,
    T_30 = 15 902 591`).

### Catalogue coverage across sequences

| atom | sources                                            |
|------|----------------------------------------------------|
| 2    | F_3, L_0, T_4                                      |
| 3    | F_4, L_2                                           |
| 5    | F_5, P_3                                           |
| 7    | L_4, T_6                                           |
| 13   | F_7, T_7                                           |
| 29   | Aurifeuillean L_1, Pell P_5, Lucas L_7 (TRIPLE)    |
| 521  | Aurifeuillean Φ_10(5), Lucas L_13                  |

**Combined coverage**: the entire catalogue `{2, 3, 5, 7, 13, 29,
521}` is reached by some sequence in
`{Pell, Lucas, Fibonacci, Tribonacci, Aurifeuillean}`.  The atom
`29` is sourced from three sequences (triple coincidence), `521`
from two (Lucas and Aurifeuillean).

**Lean**: `PellCutoff.lean` (35 PURE) + `LucasCutoff.lean` (40 PURE)
+ `FibonacciCutoff.lean` (36 PURE) + `TribonacciCutoff.lean` (28 PURE).

## §6 Direction E — Hunter complexity measure

Defines `hunterComplexity(v)` = minimum depth `k` such that `v`
admits a Hunter expression of depth ≤ `k`.

**Hierarchy** (with catalogue atom representatives):

| complexity | universe size | atoms |
|---|---|---|
| 0 | 3 (= generators) | 2, 3, 5 |
| 1 | 16 distinct values | 4, 6, 7, 8, 9, 10, 15, 25, 27, 32, 125, 243, 3125 |
| 2 | larger | 13, 29 |
| 3 | larger | 521 |

**Complexity table for catalogue atoms**:

| atom | complexity | witness                              |
|------|-----------|--------------------------------------|
| 2    | 0         | gNT                                  |
| 3    | 0         | gNS                                  |
| 5    | 0         | gd                                   |
| 7    | 1         | `2 + 5`                              |
| 13   | 2         | `(2^3) + 5`                          |
| 521  | 3         | `(2^(3^2)) + (3^2) = 512 + 9`        |

**Lean**: `HunterComplexity.lean` (32 PURE).  Explicit
`depth1Universe` list (16 values) + soundness/completeness +
complexity-hierarchy capstone.

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
| 521  | 3         | ≥ 3    |

**Lean**: `AltPrimitiveSet.lean` (28 PURE).  Demonstrates the cut-off
principle's structural content is independent of primitive choice;
the cut-off slice moves with the set.

## §8 Cross-cutting structural findings

  1. **Triple-sequence coincidence at the catalogue atom 29**:
     `Pell P_5 = Lucas L_7 = Aurifeuillean L_1 = 29`.  29 is
     triple-encoded in the Hunter catalogue
     (`d² + NT² = NT^d − NS = d² + d − 1`).  The coincidence is
     the principle's "locate" step instantiated simultaneously
     across three a-priori-unrelated external sequences.

  2. **Fibonacci embeds the entire Hunter primitive set**:
     `(F_3, F_4, F_5) = (NT, NS, d) = (2, 3, 5)` — three
     consecutive Fibonacci values are exactly the three Hunter
     generators.  Tightest possible coincidence between an
     external sequence and the 213 atomic generator set.

  3. **Lucas–Aurifeuillean coincidence at 521**: Lucas `L_13` hits
     the Aurifeuillean cyclotomic value `Φ_10(5) = 521`, the
     catalogue handle of `N_U + 1`.  Lucas hits the catalogue at
     5 indices.  Tribonacci's `T_16 = 3136` lies exactly `11`
     above `M_1 = 3125` — the tightest depth-1 boundary in the
     family, an artifact of Tribonacci's slow growth rate
     (constant ψ ≈ 1.839).

  4. **Catalogue coverage is complete**: combined hit set across
     `{Pell, Lucas, Fibonacci, Tribonacci, Aurifeuillean}` covers
     the entire catalogue `{2, 3, 5, 7, 13, 29, 521}`.  The atom
     `29` is sourced by three sequences (triple coincidence) and
     `521` by two (Lucas and Aurifeuillean).

  5. **Catalogue carries an FLT sub-closure**: under mod-p ops,
     `{(a, p) ∈ cat² : a < p}` is closed via `a^p ≡ a (mod p)`.
     15 pairs.  No general closure beyond this.

  6. **Hunter complexity is honest at 4 levels** for catalogue
     atoms, with concrete witnesses at each level.  Depth-1
     universe has exactly 16 distinct values.  The unrestricted
     depth-2 outer-pow case for `521` is closed via small-range
     decide + large-range monotonicity, promoting the depth-3
     lower bound from restricted to unrestricted.

  7. **Principle parametric in primitive set**: changing the
     primitive generators preserves methodology but shifts the
     complexity assignment of catalogue atoms (most dramatically:
     `5` moves from depth 0 to depth 1 when `d` is dropped).

## §9 Direction A unrestricted — depth-2 outer-pow case for `521` CLOSED

The previously-open outer-pow frontier of Direction A is closed
for `521` via a kernel-feasible enumeration + monotonicity split.

**Strategy** (`AurifeuilleanDepth2PowCutoff.lean`):

  · **Small range** `b ∈ {2, …, 10}` (9 values, all `< 256`
    kernel exponentiation threshold): 16 × 9 = 144 pairs
    `(a, b)`, each `a^b ≤ 3125^10 ≈ 10^35`, decide-checked.

  · **Large range** `b ∈ {15, 25, 27, 32, 125, 243, 3125}`
    (7 values): monotonicity argument
    `a ≥ 2 ∧ b ≥ 15 → a^b ≥ 2^15 = 32768 > 521`, via
    `Nat.pow_le_pow_{left,right}`.

  · **Dispatch**: split on `j.val < 9` (small) or `j.val ≥ 9`
    (large); the 16-element depth-1 universe partitions
    cleanly into the two ranges with no overlap.

**Combined verdict for catalogue prime `521`**:

  · restricted depth-2 (outer ∈ {+, *}): covered by
    `HunterComplexity.complexity_521_at_least_3_restricted`.
  · outer-pow case: covered by `AurifeuilleanDepth2PowCutoff.depth2_pow_ne_521`.

Hence `hunterComplexity(521) = 3` **without** the "restricted to
outer ∈ {+, *}" qualifier.  The upper bound (= 3) follows from
the explicit depth-3 witness `2^(3^2) + 3^2`.

## §10 Remaining frontier

  · **Direction B continuation**: extend Aurifeuillean L_m chain
    to m = 11.  Φ_{1210}(5) is 308 digits; PARI/GP `bnfisnorm`
    class-group cost grows with index.

  · **Direction C extensions**: apply principle to additional
    external sequences (Fermat numbers, cyclotomic at bases
    other than 5).  Each gives a `(f, H_k)` instance with
    different growth rates and coincidence patterns.

  · **Direction E**: extend `hunterComplexity` to a full Lean
    function with bounded search; structural complexity-hierarchy
    theorem `{v : hunterComplexity(v) ≤ k}` properly chains in k.

  · **Other catalogue atoms at depth-2-pow**: same enumeration +
    monotonicity strategy applies to `13`, `29` (already handled
    at restricted depth-2); the outer-pow case for these is a
    straightforward extension.

## §11 Cross-references

  · `cardinality_cutoff_principle.md` — methodology chapter.
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanFullCutoff.lean`
    — depth-1 cut-off substrate (28 PURE, predecessor).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanLUnbounded.lean`
    — Direction B (20 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/HunterAtomicClosure.lean`
    — Direction D (44 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanDepth2Cutoff.lean`
    — Direction A restricted (12 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanDepth2PowCutoff.lean`
    — Direction A unrestricted, outer-pow case (16 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/PellCutoff.lean`
    — Direction C, Pell sequence (35 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/LucasCutoff.lean`
    — Direction C, Lucas sequence + triple coincidence (40 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/FibonacciCutoff.lean`
    — Direction C, Fibonacci sequence + Hunter-generator window (36 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/TribonacciCutoff.lean`
    — Direction C, Tribonacci + tight near-boundary (28 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/HunterComplexity.lean`
    — Direction E (32 PURE).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AltPrimitiveSet.lean`
    — Direction F (28 PURE).
  · `theory/math/cohomology/aurifeuillean.md` — Aurifeuillean
    cyclotomic context.
  · `theory/math/dyadic_fsm.md` — Pell ↔ dyadic FSM connection.
  · `catalogs/atomic-integers.md` — Hunter atomic primes.
