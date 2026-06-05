# The LYM inequality — the per-term refinement Sperner throws away

**Reproduced result.** The Lubell–Yamamoto–Meshalkin inequality (the
Bollobás–LYM inequality): for *every* antichain `F` of the Boolean lattice
`2^[n]`,

```
Σ_{A ∈ F}  1 / C(n, |A|)  ≤  1 .
```

Sperner's `|F| ≤ C(n, ⌊n/2⌋)` is the one-line corollary: every term is
`≥ 1/C(n,⌊n/2⌋)` (the largest binomial), so the sum bounds `|F|/C(n,⌊n/2⌋)`.

**Why we picked it.** Sperner's theorem was already closed
(`sperner_double_counting.md`), and the closing went *through* the double-count
engine `lym_double_count` — but it then **immediately discarded the per-term
structure**: `sperner_upper_bound` replaces every summand by its minimum
`(⌊n/2⌋)!·(⌈n/2⌉)!` before reading off the bound. The natural question is what
the engine produces *before* that minimum is taken. The answer is LYM, a named
inequality in its own right and strictly stronger than the number it implies.
Reproducing it tests a claim about the proof-ISA: that a celebrated theorem and
its more-famous corollary are not two compilations but **one compilation read
at two resolutions** — the corollary is the inequality with one `min` applied.

## LYM is `lym_double_count` stopped one instruction early

The double-count engine is the same 0/1 incidence matrix as Sperner — rows are
antichain members `A`, columns are maximal chains `c`, the entry is "chain `c`
passes through `A`". Two readings of the one matrix:

  - **by columns:** each chain meets the antichain at most once (a chain is
    totally ordered, an antichain has no two comparable members), so the column
    sum is `≤ 1`, and the grand total is `≤ #chains = n!`;
  - **by rows:** the row for `A` counts the chains through `A`, and there are
    `≥ |A|!·(n−|A|)!` of them (order `A` internally, then order its complement).

Equate the two readings (`sumOver_swap` = Fubini) and the column bound becomes a
row bound:

```
Σ_{A ∈ F}  |A|! · (n − |A|)!   ≤   n!          -- lym_antichain
```

This is LYM **cleared of denominators**: dividing by `n!` and using
`C(n,k)·k!·(n−k)! = n!` (`binom_mul_fact`) turns `|A|!·(n−|A|)!/n!` into exactly
`1/C(n,|A|)`, recovering `Σ 1/C(n,|A|) ≤ 1`. The integer form is the honest
213-native statement — no rationals, no division; the fraction is a *reading* of
the integer inequality, not a primitive of it.

The whole content of "LYM, not Sperner" is **where you stop**. `sperner_count_bound`
takes one more instruction — `fact_mul_ge_mid`, "every term `≥` the middle term"
— and collapses the sum to `|F| · (middle term)`. LYM is the line above that
collapse. So in the compiled form the two theorems share every instruction but
the last:

```
Σ_{A∈F} |A|!(n−|A|)! ≤ n!              -- LYM            (lym_antichain)
  = double-COUNT   (the incidence matrix, two readings ; lym_double_count ∘ sumOver_swap)
  ∘ SEPARATE       (≤ 1 per chain = antichain incomparability)
  ∘ COUNT-row      (≥ |A|!(n−|A|)! chains through A ; chain_low)

|F| ≤ C(n,⌊n/2⌋)                       -- Sperner        (sperner_via_lym)
  = LYM
  ∘ min            (every term ≥ the middle ; fact_mul_ge_mid)
  ∘ cancel         (C(n,⌊n/2⌋)·(middle) = n! ; binom_mul_fact)
```

`sperner_via_lym` proves the second block literally as "apply LYM, then `min`,
then `cancel`", deriving Sperner *from the named inequality* rather than from the
engine — making "Sperner ⊂ LYM" a fact in the Lean, not a remark.

## The inequality is sharp, and the layers are exactly the extremal antichains

A bound earns the name "tight" only with a witness meeting it. A single full
layer `kLayer n k` (`k ≤ n`) does: every member has `|A| = k`, so every term is
`k!·(n−k)!`, and there are `C(n,k)` members, so the sum is
`C(n,k)·k!·(n−k)! = n!` — equality (`lym_tight_layer`). So LYM holds with
equality *exactly* on the layers: the `min`-step in Sperner is lossless precisely
when the antichain sits in one layer, which is why the extremal Sperner families
are the middle layer(s) and nothing else. The corollary's slack is the
inequality's per-term gap, and the gap closes iff `F` is uniform.

This is the same lesson as the absorption identity in `sperner_double_counting`:
the *number* `C(n,⌊n/2⌋)` is a READ followed by unimodality, and here the
*equality case* is the same READ — a layer's LYM sum is `C(n,k)·k!·(n−k)!`,
which `binom_mul_fact` says is `n!` on the nose, no inequality at all.

## The answer to "why"

LYM is not a second theorem about antichains. It is the cardinality of one
finite incidence residue (subsets × chains) written as two sums, with the column
sum capped at `1` per chain — i.e. the `COUNT` instruction's double-count face,
reported *without rounding each row down to the worst case*. Sperner is that same
report with one rounding applied. The proof-ISA claim survives the test: the
move is `COUNT`, the named inequality and its named corollary differ by a single
`min`, and which theorem you have is which line of the compilation you read.

## Witnesses

  - `lean/E213/Lib/Math/Combinatorics/LymInequality.lean` — `lym_inequality`
    (engine form), ★★ `lym_antichain` (the named inequality, unconditional),
    `lym_tight_layer` (the equality case / sharpness), `sperner_via_lym`
    (LYM ⟹ Sperner), `lym_tight_examples`.  5/5 PURE.
  - the engine and arithmetic it stops short in:
    `Lib/Math/Combinatorics/Sperner.lean` — `lym_double_count`, `sumOver_swap`,
    `fact_mul_ge_mid` (the discarded `min`), `binom_mul_fact` (the `1/C` reading
    and the cancel), `kLayer_card`, `kLayer_isAntichain`.
  - the chain model discharging the two counts:
    `Lib/Math/Combinatorics/SpernerChains.lean` — `chains_length` (= `n!`),
    `chain_cap` (≤ 1 per chain), `chain_low` (≥ `|A|!(n−|A|)!` per member).
  - the corollary it refines: `sperner_double_counting.md`,
    `SpernerChains.sperner` / `sperner_theorem`.
  - instruction set: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`.
