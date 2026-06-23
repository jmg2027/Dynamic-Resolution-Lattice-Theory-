# Frontier: the invariant structure of the decomposition calculus

**Status**: active synthesis thread (2026-06-23). **Tier**: 1.
Anchor: `research-notes/decomposition/SYNTHESIS.md` §2 "Five structural findings".

The decomposition calculus runs on **two named invariants** — A (character arrow
`×↦·`/`×↦+`) and B (the `q=±1` residue tag).  This session's residue-Lens arc
(`prime_distribution`/`modular_arithmetic`/`gcd_euclidean`/`computability_halting`/
`cayley_dickson`/`frobenius_endomorphism`, #136–141) produced five findings on
how the invariants are actually structured (SYNTHESIS §2 (i)–(v)).

## Settled this session

- **(iv) A↔B relation**: B = A's unimodular 2-torsion where a character exists
  (Legendre = the character into {±1}); the bare diagonal escape where none does.
  B has broader *domain*; A is *richer* where both live.  Not "A a face of B".
- **(v) the modulus is NOT a third invariant**: it is the finite signature of B's
  `q=+1`-reached-by-none pole (Banach / irrational-CF / continuum cuts), absent
  for faithful Lenses and for discrete escapes.  One tag (B), two specialisations
  (A multiplicative-enrichment, modulus reached-by-none-signature).
- **Frobenius (#141)** = A's collapse point (×↦· and +↦+ become one self-map
  `(·)ᵖ`); its `q=+1` fixed pole = the fixed field 𝔽_p (Fermat).

## Open directions (next)

1. **Is B genuinely irreducible, or does it have its own sub-structure?**  B's two
   poles (escape/converge) are clear; is there a finer invariant *within* a single
   pole beyond the modulus (e.g. the *order* of escape — pole-order / difference-
   depth, cf. `simplicial_operation_tower.md` L3‴)?  Test whether "pole-order" is a
   graded refinement of B or a re-reading of the modulus.
2. **The character-free residues** (foundations: Cantor/Gödel/halting/measure) —
   do they ALL reduce to the one Lawvere diagonal, or are there character-free
   residues that are NOT the diagonal?  (Measure/non-measurable = a calibrated
   boundary, not obviously the diagonal — test.)
3. **A's collapse points beyond Frobenius**: are there other places ×↦· and +↦+
   coincide (char-p Frobenius is one; the `q=+1` trivial-character is another)?
