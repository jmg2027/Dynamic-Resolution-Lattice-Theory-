# Information 213 — Module Index

Blueprint: `blueprints/math/12_information_213.md`.

## Atomic foundations

| File | Topic | Status |
|---|---|---|
| `Bit.lean` | bitDepth, bitsAfterBisections, log₂(2^n) = n atomic | ∅-axiom |
| `Entropy.lean` | shannonEntropyUniformBits, surpriseBitsDyadic, dyadicProbabilityCut | ∅-axiom |

## Joint + divergence

| File | Topic | Status |
|---|---|---|
| `MutualInfo.lean` | jointEntropy, mutualInfoIndependent (= 0), self-mutualInfo = entropy | ∅-axiom |
| `KLDivergence.lean` | klBitsDyadic = depth difference, self-KL = 0, non-negativity | ∅-axiom |

## Channel + coding

| File | Topic | Status |
|---|---|---|
| `Channel.lean` | noiselessChannel = 1, BSC capacity (atomic dyadic) | ∅-axiom |
| `Coding.lean` | hammingDistance + self-distance 0; optimalCodeLength = log alphabet | ∅-axiom |

## Kolmogorov

| File | Topic | Status |
|---|---|---|
| `Kolmogorov.lean` | kolmogorov_213 = 4 (Raw axiom clauses); axiom minimality | ∅-axiom |

## Synthesis

| File | Topic | Status |
|---|---|---|
| `Capstone.lean` | 7 cluster witnesses + total_witness | ∅-axiom |
| `Information.lean` | umbrella | — |

## Atomic content highlights

  * **bit = bisection**: Δ⁴ depth-`n` bracket carries exactly `n`
    bits.  No real-valued log; the depth IS the log atomically.
  * **`H(uniform on 2^n) = n bits`**: foundational identity, rfl.
    No Shannon limit, no `lim` operator — direct equality on
    dyadic substrate.
  * **Mutual info of independent uniforms = 0**: additivity via
    `Nat.sub_self`.
  * **KL divergence**: depth difference between two dyadic
    distributions, clamped to 0 (Jensen's inequality
    automatically via `Nat.zero_le`).
  * **Noiseless channel capacity = 1 bit/symbol** (rfl).
  * **K(213) = 4**: the Raw axiom's 4 clauses are the minimum
    description of the entire 213 framework — Kolmogorov-minimal
    by construction (cf. `seed/AXIOM/04_falsifiability.md`
    §5.2.1: any extra axiom = theory falsified).

## Next continuations (out of scope here)

  * Quantum information (qubit, von Neumann entropy via cohomology
    grading).
  * Universal Turing machine 213-encoding (AIT).
  * Channel coding lower bound (Shannon converse) — needs general
    real-valued log for non-dyadic distributions; on dyadic
    substrate, it's already tight.
