# G123 — Real213-p-adic post-closure: next directions

**Context**: G122 closed (Padic library 308 PURE / 0 DIRTY across 8
modules).  Headline closures: ring axioms at trunc, Hensel inv/sqrt
existence + uniqueness, full ultrametric, Frobenius lift, Teichmüller
Cauchy, ℚ_p arithmetic, DRLT 5-adic anchor.  See
`theory/math/padic_real213.md` for the narrative.

This note records candidate next directions for follow-up campaigns.
Each entry includes: statement, dependency chain, estimated
difficulty, and a note on 213-native angle.

## Status (updated post-A/B campaign)

- **A — Explicit Teichmüller representative `ω(x)`: CLOSED.**
  `Zp.teichmuller` (diagonal of the iteration `x ↦ x^p`) +
  `teichmuller_pow_p_trunc` (the Frobenius fix `ω^p ≡ ω`) in
  `Padic/Teichmuller.lean`.  Simpler than anticipated: the Cauchy
  lemma `teichmuller_iter_cauchy` IS the diagonal trunc-recursion, so
  *no separate digit-stability lemma was needed* (unlike `invFull`).
- **B — `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)`: CLOSED at trunc level.**
  `teichmuller_pow_pred_trunc` (`ω^(p−1) ≡ 1`, root of unity) +
  `teichmullerCofactor` / `teichmullerCofactor_trunc_one`
  (`u = ω⁻¹·x ≡ 1 mod p`) in `Padic/TeichmullerUnit.lean` (bridges
  Teichmuller + Hensel).  Remaining open: sequence-level uniqueness of
  the `ω·u` split (same caveat as direction C — sequence-level equality
  may be a non-213-native question).

Next on-path candidates: **G** (general `Zp.div`), then **H** (DRLT
5-adic content).

## A. Explicit Teichmüller representative `ω(x)`

**Statement**: construct `Zp.teichmuller p hp x sb : ZpSeq p` such that
- `(Zp.teichmuller p hp x sb).digits 0 = sb.d_0`,
- `Zp.mul (Zp.teichmuller p hp x sb) (Zp.teichmuller p hp x sb) ... = ω(x)`
  (idempotent under raising to p-th power),
- specifically: `(Zp.pow (teichmuller x) p).trunc n = (teichmuller x).trunc n` for all n.

**Construction**: diagonal extraction from `teichmuller_iter`, parallel
to `invFull` / `sqrtFull`:
```
def teichmuller (...) : ZpSeq p where
  digits k := (teichmuller_iter p hp x k).digits k
```

Need: prove digit stability (analog of `invSeq_digit_stable`) for
the iteration.  Then `teichmuller_iter_cauchy` gives that the
diagonal sequence stabilizes.

**Difficulty**: medium.  Mirrors `invFull` / `sqrtFull` construction.
~150 lines estimated.

**213 angle**: clean — uses only existing infrastructure (`pow`,
`teichmuller_iter`, `teichmuller_iter_cauchy`).  Adds the limit
object that classical theory introduces via projective limit.

## B. Multiplicative group decomposition `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)`

**Statement**: every unit `x ∈ ℤ_p` factors uniquely as `x = ω · u`
where `ω` is a `(p−1)`-th root of unity (Teichmüller representative)
and `u ≡ 1 (mod p)`.

**Construction**: `ω := teichmuller x sb`, `u := x · ω⁻¹` (using
`invFull`).  Verify `u.digits 0 = 1`.

**Difficulty**: medium-low (given A).  ~50 lines.

**213 angle**: produces a concrete decomposition theorem; useful for
DRLT if units of `ℤ_5` carry meaning at the resolution boundary.

## C. Sequence-level ring axioms

**Statement**: `Zp.add x y = Zp.add y x` AS `ZpSeq` (not just at
trunc).  Similarly assoc, distrib.

**Difficulty**: high.  Requires either:
- propext / Quot.sound infrastructure (violates ∅-axiom standard),
- or a digit-wise propositional equality after careful convolution
  reindexing for `mulRaw x y k = mulRaw y x k`.

**213 angle**: it's an open question whether sequence-level equality
is even the "right" 213-native notion.  Trunc-level equality is
arguably more native (matches finite-resolution reading).  Worth
revisiting `seed/RESOLUTION_LIMIT_SPEC.md` for guidance — perhaps
sequence-level equality is an *imported residue* that 213 should
not chase.

**Recommendation**: defer or reframe.

## D. Witt vectors as `ZpSeq p` generalization

**Statement**: define `WittSeq R p` for a ring `R`, where `R = Fin p`
recovers `ZpSeq p`.

**Difficulty**: high.  Requires ring-of-rings infrastructure.

**213 angle**: Witt vectors are the canonical "deformation" of
characteristic-p rings.  Of interest if DRLT later wants to consider
"deformations" of the count-Lens at level 2.  Otherwise abstract.

**Recommendation**: low priority for DRLT.

## E. Local fields and ramification

**Statement**: define totally ramified extensions of ℚ_p via Eisenstein
polynomials; show `[K : ℚ_p] = e · f` (ramification × residue degree).

**Difficulty**: very high.  Requires polynomial rings, irreducibility,
algebraic extensions — all of which need their own ∅-axiom
infrastructure.

**213 angle**: not obvious.  Local fields are "classical" structure;
DRLT operates one level below (the count-Lens itself).

**Recommendation**: very low priority.

## F. p-adic analytic functions (Mahler basis)

**Statement**: define continuous `f : ℤ_p → ℤ_p` via Mahler series
`f(x) = ∑ aₙ · C(x, n)` where `C(x, n)` is the binomial coefficient.

**Difficulty**: very high.  Requires binomial coefficients (which we
specifically avoided), continuity in p-adic metric, infinite sums.

**213 angle**: continuous functions don't translate cleanly into 213's
finite-resolution count-Lens picture.  Would need a custom 213-native
notion of "p-adic continuity" (which might end up being "trunc-level
agreement at every level").

**Recommendation**: speculative.

## G. ZpSeq.div (general division, not requiring unit)

**Statement**: `Zp.div x y` defined for any `x, y` (not just unit `y`),
returning a `QpSeq p` rather than `ZpSeq p` (allowing negative shift).

**Difficulty**: medium.  Use `valEq` to compute the shift; reduce y
to unit form before applying `invFull`.

**213 angle**: completes the field-of-fractions picture for ℚ_p.
Cleanly extends existing `QpSeq.inv` / `QpSeq.div`.

**Difficulty**: ~80 lines.

## H. DRLT-specific 5-adic content

**Statement**: investigate whether the 5-adic Real213 carries content
beyond the resolution limit `N_U = 5²⁵`.  Specifically:

1. Is there a 5-adic obstruction to any DRLT precision result?
2. Does `i_5 = √(-1) ∈ ℤ_5` carry physics meaning (5-adic spinors? 5-adic CP-violation?)?
3. Are there 5-adic L-values relevant to DRLT constants (α_em, m_μ/m_e)?

**Difficulty**: open-ended; research, not closure.

**213 angle**: This is where the campaign's effort might most pay back
toward DRLT.  The 5-adic envelope IS the natural extension of
`N_U = 5²⁵` — does it operate meaningfully, or is it formal residue?

**Recommendation**: highest research interest if revisited.

## Prioritization

For follow-up campaign (when resources permit):

1. **A** (explicit ω) and **B** (mult group decomp): natural completions
   of what we have; small effort relative to existing investment;
   make the library "feature-complete" for textbook ℤ_p^× theory.

2. **G** (general ℚ_p division): completes the field picture cleanly.

3. **H** (DRLT-specific 5-adic content): high-value research question;
   open-ended.

4. Defer / reframe **C** (sequence-level equality): may not be the
   right 213-native question.

5. Skip **D** (Witt), **E** (local fields), **F** (Mahler) unless
   DRLT specifically demands them.

## Methodological lessons (for future ∅-axiom marathons)

From the G122 marathon:

- **Find binomial-free proofs**.  The Frobenius lift via geometric
  sum was a discovery forced by avoiding binomial coefficients.
  Similar simplifications may exist elsewhere — e.g., in Euler's
  theorem, Wilson's theorem, etc.

- **Cancel via the inverse**.  Hensel uniqueness, sqrt uniqueness,
  cancellation-by-units all flow from one lemma:
  `(invFull x · x).trunc = 1`.  This pattern is robust and will
  recur in any ring-with-units context.

- **Diagonal extraction for limits**.  `invFull`, `sqrtFull`,
  hypothetical `teichmullerFull` — all use the same template:
  `digits k := (approxSeq k).digits k`.  Worth abstracting as a
  general "p-adic limit" construction if we need more such objects.

- **congrArg for selective rewriting**.  When `rw [h_eq]` would
  mass-substitute, `congrArg f h_eq` gives surgical control.  In
  propext-permissive worlds this would be `simp only [h_eq, ...]`
  with position restrictions.

- **`set` is unknown; use `let` or inline names**.  Small Lean-elab
  quirk, but noted for next time.

## How to use this note

Treat as a roadmap, not a contract.  If a follow-up campaign starts,
pick one bullet from §A–§H, copy this note's relevant section into
the new campaign's research-notes, and proceed.  Or pursue something
unlisted that the prior closure has now unlocked.

Source for the closures referenced: `lean/E213/Lib/Math/Padic/*`,
chapter `theory/math/padic_real213.md`, catalog entry in
`STRICT_ZERO_AXIOM.md`.
