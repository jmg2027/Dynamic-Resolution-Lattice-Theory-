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

## Settled by the multi-agent push (2026-06-23) → SYNTHESIS §2 (vi),(vii)

1. **Is B reducible? — NO** (`invariant_structure/graded_q.md`).  B is a sign/direction
   bit, the order-2 truncation of *neither* the multiplicative `q^k=1` cyclic grading
   (which lives inside B's converge pole; the escape pole has no `q^k=1` reading) *nor*
   the additive depth grading (`ε²=0`/`vp`/pole-order, an orthogonal axis).  The two
   gradings are themselves Invariant A (`×↦·`/`×↦+`) one level up.  Calibrated negative.
2. **Character-free residues — two faces of one B** (`invariant_structure/character_free_residues.md`).
   The Lawvere diagonal (∅-axiom THEOREM; Cantor/Gödel/Russell/halting all reduce) and
   the LLPO/choice/ultrafilter point (non-constructive `Prop`, never proved; the 5
   calibrated boundaries' single locus) are the internal/constructive and
   external/refused faces of one B, split by **axiom-status**.

## Open directions (next)

3. **A's collapse points beyond Frobenius**: are there other places `×↦·` and `+↦+`
   coincide (char-p Frobenius is one — `frobenius_endomorphism.md`; the `q=+1`
   trivial-character is another)?  Is there a *classification* of A-collapse loci?
4. **B's escape pole, finer?**  (vi) shows the converge pole carries the cyclic grading;
   does the *escape* pole carry internal structure beyond "universal negation", or is it
   genuinely featureless (the pure diagonal)?  (vii) suggests featureless — confirm.
5. **The exp/log wall as the A-grading separator**: (vi) found the cyclic (`ℤ/k`) and
   free (`ℕ`) gradings are exp/log-wall-separated.  Is the wall itself an invariant-level
   object (the boundary between A's two arrows)?
