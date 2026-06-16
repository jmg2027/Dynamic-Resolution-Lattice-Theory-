# When ∅-axiom forces a different proof (collection)

A running collection, per the originator's criterion: not "classical theorem,
PURE proof" (which is usually `(standard proof) − (axiom import)` =
bookkeeping), but **theorems where requiring ∅-axiom forces a *structurally
different* proof — and the difference reveals something** (an explicit
witness / algorithm / representative-level operation the classical proof hid).

The discriminator (a case only counts if BOTH hold):
1. the standard textbook proof uses a non-constructive / quotient / impredicative
   principle in a **load-bearing** way (not just because the ambient library is
   built on it), AND
2. the ∅-axiom route is **not** the same proof with lemmas swapped — its shape
   changes, and the new shape exposes constructive content.

Excluded (the bookkeeping kind, deliberately not collected): swapping
`Nat.dvd_trans`→`dvd_trans_213`, `rw`-on-`Iff`→`.mp/.mpr`, `funext`→pointwise,
`Nat.mul_mod_left`→`NatDiv213.…`. Real but not revealing.

## Three veins of genuine forcing

- **A — Quot.sound avoidance.** Theorem classically stated on a *quotient*
  (ℤ = ℕ² quotient, ℚ = pair quotient, ℤ/n, group quotients), proven on
  *representatives*. Reveals: the quotient was packaging; the operation lived
  on the representative all along ("the tuple IS the number",
  `theory/math/numbersystems/slot_arithmetic.md`).
- **B — Classical / LEM avoidance.** An existence theorem classically proved by
  *minimal counterexample / `by_contra`* (LEM + well-ordering), re-proven by
  *explicit descent / bounded search*. Reveals: the witness / algorithm.
- **C — non-effective→effective.** A statement whose classical form is
  non-effective (an existential with no extraction), forced into a *modulus /
  constructor* form. Reveals: the rate / the construction. (The corpus modulus
  programme; `Math/Logic/` omniscience hierarchy is the meta-catalog of exactly
  where classical imports — LLPO/WKL/König/Heine-Borel.)

## Seeded cases (this session) — honest about which genuinely force

### B — Euler's theorem `a^φ(n) ≡ 1 (mod n)` (★ clearest genuine forcing)
`NumberTheory/EulerTheorem`. The natural route — "the order of `a` divides
`φ(n)` (Lagrange), and `a^ord = 1`" — is **circular for composite n**: the
corpus's order theory is prime-specific and "order ∣ φ(n)" for composite n
*needs Euler itself* (it became iter-174 `MultiplicativeOrder`, downstream of
Euler). So ∅-axiom forced the **totative-product permutation** proof: `x ↦ ax`
permutes the units, so `∏(units)` is `LPerm`-invariant ⟹ `a^φ·P ≡ P` ⟹ cancel.
Reveals: Euler is essentially a **permutation-invariance** fact, not a Lagrange
corollary — the group-order packaging hid that for composite moduli.

### B — `exists_nontrivial_factor` (in Wilson's converse)
`ModArith/WilsonConverse`. Classical "least divisor > 1 is prime" is
well-ordering + `by_contra`. The PURE route used `exists_prime_factor`
(bounded search) — the factor is an **explicit, computed** object, not an
abstract minimum.

### B/C — τ-parity & σ-parity via `doubleSum_parity`
`NumberTheory/TauParity`. The textbook "divisors pair `d ↔ n/d`, count mod 2"
becomes, ∅-axiom, the **symmetric double-sum parity** lemma `Σ_{a,b<N} g a b ≡
Σ_a g a a (mod 2)` (off-diagonal pairs cancel). Reveals: the parity is a
**fixed-point count** of the Z/2 involution, computed, not read off a
multiplicativity table. (Partial: the multiplicativity *could* also be
factored; the forcing is in choosing the involution-count form.)

### A (candidate, not yet a clean case)
The number-system corpus already works representative-first (Padic digits, slot
arithmetic, ℤ-as-difference-Lens). Need a theorem *classically iso-on-a-quotient*
re-proven as an *explicit bijection* to make a sharp A-case — see forward hunt.

## Forward hunt (targets selected by the criterion)

- **A**: a theorem classically a *quotient-ring isomorphism* (CRT `ℤ/mn ≅
  ℤ/m × ℤ/n`, or a first-iso instance) re-proven as an **explicit reconstruction
  bijection** on representatives — reveals the iso *is* an algorithm. (Check
  `ModArith/LensCRT` for overlap first.)
- **B**: classical results whose only textbook proof is minimal-counterexample
  — and whose descent witness is interesting (not just "a factor exists").
- **C**: a classically-non-effective existence (an "∃ by compactness") whose
  ∅-axiom form needs a modulus, where the modulus is the content.
- **The sharpest test**: take a theorem the corpus *currently has DIRTY*
  (axiom-carrying) and ask whether a PURE re-derivation forces a different
  proof. `tools/scan_all_axioms.py` + `STRICT_ZERO_AXIOM.md` locate the DIRTY
  set; those are the highest-signal candidates (the corpus already judged them
  worth stating; PURE-ifying tests whether the residue supports them *its* way).

## Why this is the better selector
Per `seed/AXIOM/07_primacy.md §7.1`, derivation *confirms* primacy. But a PURE
re-derivation that is mere bookkeeping confirms only that the *library's* axiom
use was incidental — weak evidence. A PURE re-derivation that **forces different
mathematics** is the strong form: it shows the residue reaches the result *by a
route classical math doesn't take*, i.e. the result was always residue-native,
the classical packaging non-essential. Those are the cases worth collecting.

Promotable to `theory/meta/` (a methodology chapter) once ≥ ~5 sharp cases
across ≥ 2 veins are pinned.
