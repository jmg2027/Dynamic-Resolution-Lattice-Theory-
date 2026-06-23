# Decomposition: prime distribution (where the ×-atoms fall on the +-line)

*213-decomposition of "prime distribution / Bertrand's postulate", per `../README.md`.*

This is the **dual** of `prime_factorization.md`.  There the object is a *number* `n`, the reading is
`L_vp` (its prime-exponent vector), and the residue is **none** — `L_vp` is faithful, and that
zero-residue *is* unique factorization.  Here the object is the **basis that `L_vp` presupposes**: the
primes themselves, as **positions on the additive line `ℕ`**.  The multiplicative reading reads every
number *over* that basis but does **not** generate or locate it; the location of the ×-atoms on the
+-line is the residue the multiplicative construction leaves.  That residue is **not** none — it is the
prime-gap structure — and **Bertrand's postulate is a `q=+1` bound on it.**

## The decomposition

- **Construction `C`** — `ℕ_{>0}` under the **×-construction** (same as `prime_factorization.md`):
  numbers built by multiplying ×-atoms.  The ×-atoms (primes) are the *distinguishable* irreducibles
  (`Meta/Nat/UnitList.lean:append_comm` makes the +-atom — the unit — indistinguishable; the ×-atoms
  are its dual, each carrying its own `vp`-coordinate).
- **Reading `L`** — the **basis-locator**: not "read a number over the primes", but "**which positions
  `p ∈ ℕ` are ×-atoms?**" — the primality indicator `IsPrime213`, and its running count `primesIn`/`π`.
  This Lens points at the *basis* of `L_vp`, not at a number's coordinates in it.
- **Residue `⊕`** — the **distribution of the atoms on the +-line**: the gaps `pₖ₊₁ − pₖ`, the count
  `π(x)`, *where* the next atom is.  The ×-construction fixes *which* numbers are atoms (a `×`-fact:
  no nontrivial factorization) but says **nothing additively** about *where* they land (`n, n+1, …` is a
  +-fact).  That mismatch — atoms defined by `×`, located on `+` — is the residue.  It is genuinely
  non-trivial: the construction does not predict it, and it never terminates (`exists_prime_gt`: the
  basis is infinite, the residue re-enters forever).

## Re-seeing the theorems

The residue has **two faces**, the standing `q=±1` tag:

- **`q = +1` (bounded / converge side) — Bertrand.** "There is always a prime in `(n, 2n]`" is exactly
  *"the additive gap to the next ×-atom is bounded by `n`"* — the residue never opens wider than a factor
  of 2.  This is the converge-side tag (a bracket that always closes), the prime analogue of
  `golden_is_converge` / the `q=+1` contraction family.
- **`q = −1` (escape side) — arbitrary gaps.** Between specific atoms the residue *does* open
  arbitrarily wide: `n!+2, …, n!+n` are all composite, a gap `≥ n`.  The escape-side tag (the bracket
  that runs away), the prime analogue of `escape_residue_outside`.

Bertrand is therefore not "a theorem about numbers" but **a bound on the `L_vp`-residue**: the
distinguishable ×-atoms cannot cluster so sparsely that the doubling window `(n, 2n]` is empty.

## Revelation (collapse + forcing)

**Collapse — "multiplicative vs additive number theory" is one residue, read two ways.**  The split the
field calls *multiplicative* (factorization, `vp`, Dirichlet) vs *additive* (gaps, counting, sieves)
number theory is not two subjects: it is the ×-construction (`C`) and its `L_vp`-residue (the +-located
basis).  `prime_factorization.md` is the `C`/`L_vp`-side (residue none); *this* note is the residue
itself.  One object, the two halves of `⟨C|L⟩ ⊕ Residue`.

**Forcing — Erdős's proof is the character arrow `×↦+` turned into a constraint on the residue.**  The
whole proof is: *read* `C(2n,n)` through the ×-count-Lens (`central_binom_factorization`:
`C(2n,n) = ∏_{p ≤ 2n} p^{vₚ}`, an instance of the explicit reconstruction `prod_prime_pow_eq`), bound
each ×-atom's block (`central_binom_upper_bound`: `≤ 4^{2n/3}·(2n)^{√(2n)}`), and **collide it with the
+-size** of the same object (`four_pow_le_succ_mul_central_binom`: `4ⁿ ≤ (2n+1)·C(2n,n)`).  The ×-reading
and the +-size of *one* number `C(2n,n)` are forced to agree, and that agreement **bounds the residue**
(`exists_prime_in_window`): if the window `(n,2n]` held no atom, the ×-reading would be too small for the
+-size.  The character bridge `×↦+` (the same `vp_mul` arrow as everywhere) is the *mechanism* that
converts a multiplicative fact (factorization of `C`) into an additive one (a gap bound) — the residue
made computable.

This re-reads the entire `vp`/Bertrand Lean layer **not as a formalization of Erdős, but as the
surfacing of the `L_vp`-residue**: each lemma is a statement about the ×-atoms' +-distribution.

## Verified Lean anchors (file:line:theorem — grep-confirmed, scans from repo root this session)

The Lens and its faithfulness (the basis coordinate):
- `Meta/Nat/VpSeparation.lean:172` `vp_separation` — `L_vp` injective (the basis is a *faithful*
  coordinate system; what makes "over the primes" well-defined).  **PURE.**
- `Meta/Nat/VpMul.lean:165` `vp_mul` — the `×↦+` character arrow (`vp(ab)=vp a+vp b`); `:183` `vp_pow`.
  **PURE.**

The explicit reconstruction (the ×-count-Lens reads the *whole* basis) — built this session:
- `Lib/Math/NumberTheory/PrimePowFactorization.lean` `prod_prime_pow_eq`
  (`m = ∏_{p≤B,prime} p^{vₚ(m)}`), `primePowProd_le_pow_length`, `primePowProd_le_listProd`,
  `primesIn_length_le`, `mem_primesIn`.  **PURE (10/0).**

The residue bound (Bertrand) — built this session:
- `Lib/Math/NumberTheory/CentralBinomFactorization.lean` `central_binom_factorization`
  (`C(2n,n)=∏_{p≤2n} p^{vₚ}`); `central_binom_factorization_le_two_thirds` (the no-atom-in-`(n,2n]`
  collapse to `≤2n/3`); `central_binom_upper_bound` (`C(2n,n) ≤ 4^{2n/3}·(2n)^{√(2n)}`);
  **`exists_prime_in_window`** (the `q=+1` gap bound, modulo the crossover).  **PURE (8/0).**

The `+`-size lower bound and the atom-density bound (the collision):
- `Lens/Number/Nat213/MultSystemValue.lean:507` `four_pow_le_succ_mul_central_binom`
  (`4ⁿ ≤ (2n+1)·C(2n,n)`, the +-size); `:470` `central_binom_ge_two_pow`.  **PURE.**
- `Lib/Math/NumberTheory/Primorial.lean:102` `primorial_le_four_pow` (`∏_{p≤N} p ≤ 4ᴺ`, the ×-atom
  density ceiling).  **PURE.**

Infinitude (the residue never terminates):
- `Lens/Number/Nat213/MultSystemValue.lean:689` `exists_prime_gt` (`∀N, ∃ p prime, N<p`) — the basis is
  infinite; the `L_vp`-residue re-enters forever (the prime instance of the residue's perpetual
  re-entry, the `escape`-pole of `ResidueTag.residue_tag_two_poles:228`).  **PURE.**

## BUILT vs ABSENT

- **BUILT (`q=+1` side, ∅-axiom):** the entire *structural* content of the gap bound — the explicit
  ×-reading of `C(2n,n)`, its upper bound, and the reduction `exists_prime_in_window` of Bertrand to two
  pure-`Nat` facts (`√(2n) ≤ 2n/3`; the crossover `(2n+1)·4^{2n/3}·(2n)^{√(2n)} < 4ⁿ`).
- **ABSENT (predicted-not-built):** (i) the crossover asymptotic (`n ≥ N₀`) + the finite prime chain
  (`n < N₀`) — the *arithmetic* residue-bound, pure-`Nat`, no new ingredient (frontier
  `bertrand_postulate.md`); (ii) the `q=−1` escape statement `∀N, ∃ gap ≥ N` (`n!+2..n!+n` composite) —
  the residue's other face, predicted from the tag, not yet a Lean theorem; (iii) `π(x) ∼ x/ln x` (PNT) —
  the *fine* shape of the residue, a `Real213`-limit object (the residue's pointing, reached by none).

## Touches the model?

**No new primitive; this is the residue half the corpus had under-read.**  The two standing invariants
hold verbatim: the character arrow is `vp_mul` (`×↦+`), and the `q=±1` tag splits the prime-gap residue
into Bertrand (bounded, `+1`) vs arbitrary gaps (escape, `−1`).  The new datum is the *re-framing*: the
`vp`/Bertrand Lean layer, built as a formalization of Erdős, is properly read as the **surfacing of the
`L_vp`-residue** — the additive distribution of the multiplicative atoms — completing the dual of
`prime_factorization.md` (where that residue was none *for a fixed number*; here it is the whole content
*for the basis*).
