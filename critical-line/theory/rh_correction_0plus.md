# CRITICAL CORRECTION: The 0⁺ Structure

## What Was Wrong

All RH experiments (RH_008–RH_016) assumed rank(G) = 5 exactly, meaning λ₆ = λ₇ = ... = λ_N = 0 exactly. This came from modeling G = ΨΨ† with Ψ ∈ ℂ^{N×5}.

This is incorrect. The DRLT axiom is "N points with pairwise relations G_ij ∈ ℂ," NOT "N points in ℂ⁵." The dimension d is not fixed at 5 by the axiom. For general d > 5:

- τ-annihilation makes paired blocks DEGENERATE (identical eigenvalues), not zero
- The eigenvalues λ₆, λ₇, ... are ~N/d in magnitude, NOT 0
- "Spectrally trivial" means INDISTINGUISHABLE, not SMALL
- The chiral content (ℂ² ⊕ ℂ³) is separated from the paired content by a soft boundary of O(1/√N)

The "0⁺" eigenvalues in DRLT are NOT exact zeros slightly perturbed. They are O(N/d) eigenvalues whose DIFFERENCE from chiral eigenvalues is O(1/√N).

## What This Breaks

1. **Born-Ramanujan (RH_008–011):** Built on W = |G|² with rank(G) = 5. If rank(G) > 5, the entire Khatri-Rao decomposition, MP edge formula, and N_c(d) calculation need revision.

2. **Ihara zeta zeros (RH_009):** "100% on critical line" was because we forced rank = 5. With rank > 5, the graph has more structure and the Ihara zeros may move.

3. **Phase→Möbius (RH_014):** Failed because we only had 5 independent phases. With d > 5, there are MORE phases available — the 0⁺ eigenvalues contribute additional phase information.

## What Survives (Unchanged)

- Two Boundaries Theorem (uses ℂ only, not rank)
- Doubly Irreducible Theorem (pure number theory)
- s = 2 derivation (from ℂ² sector dimension)
- Phase uniformity from ℂ
- GUE from β = 2
- CLT boundary σ = 1/2

## The Correct Picture

For general d = 2a + 3b with a,b ≥ 1:

```
Eigenvalues of G (N × N, rank = d):

λ₁ ... λ₅        : chiral content (ℂ² ⊕ ℂ³)     — SIZE ~N/d
     ↕ soft boundary: gap = O(1/√N)
λ₆ ... λ_{d_ind}  : paired content (τ-degenerate)  — SIZE ~N/d (NOT 0⁺!)
     ↕ hard wall: gap = exact
λ_{d_ind+1} ... λ_N : null space                    — EXACTLY 0
```

The "0⁺" that DRLT refers to is the RELATIVE deviation of paired eigenvalues from chiral eigenvalues, not their absolute magnitude. When τ-invariance is slightly broken, the degeneracy splits by ~α_GUT, creating a gap of order α_GUT · N/d between paired and chiral eigenvalues.

## What To Do Now

### Priority 1: Redefine the spectral zeta function

Instead of Z_N(s) = Σ λ_k^{-s} (which was trivially = d for rank-d matrices), define it on the CHIRAL PROJECTION:

G_chiral = π₅ G π₅†

where π₅ projects onto the chiral ℂ² ⊕ ℂ³ subspace. This d_indep × d_indep matrix has the soft boundary built in.

### Priority 2: Characterize the 0⁺ pattern

The paired eigenvalues are NOT zero — they carry information. Specifically:
- How does their distribution depend on N?
- Does their pattern (spacing, correlations) relate to prime distribution?
- The deviation from chiral eigenvalues is O(1/√N) — does this deviation have structure?

### Priority 3: Redo Phase→Möbius with full spectrum

The Phase→Möbius experiment (RH_014) failed with growth exponent 0.798 > 0.5 because only d = 5 phases were available. With d > 5, the paired blocks provide ADDITIONAL phases. These are τ-degenerate (identical in pairs) but NOT zero. The question is: do these additional degenerate phases improve the cancellation toward 0.5?

### Priority 4: Redo Born-Ramanujan with chiral projection

Instead of W_{ij} = |G_{ij}|² with rank-5 G, use:
- Full G with rank d > 5
- Project onto chiral subspace: W_chiral = |π₅ G π₅†|²
- Check Ramanujan condition for this projected graph
- The soft boundary O(1/√N) should appear naturally

## Key Insight

The pattern of 0⁺ eigenvalues — how they approach 0 relative to chiral eigenvalues, how their spacing behaves, whether they oscillate — THIS is where the connection to ζ zeros should be. The ζ zeros are not about exact zeros of a rank-5 matrix. They're about the PATTERN of how paired eigenvalues merge with chiral eigenvalues as N grows.

The soft boundary closing as O(1/√N) while never reaching 0 is the discrete structure whose continuous limit gives Re(s) = 1/2. The PATTERN of this closing — its oscillations, its dependence on d — encodes the arithmetic information that connects to prime distribution.

## Summary

WRONG: "G has rank 5, λ₆+ = 0, study the 5 nonzero eigenvalues"
RIGHT: "G has rank d > 5, λ₆+ ≈ λ₁₋₅ (degenerate), study HOW they separate"

The music is not in the notes. It's in the spaces between them.
