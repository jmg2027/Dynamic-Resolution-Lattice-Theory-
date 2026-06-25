# Regrounding is a readout, not a re-derivation

To reground a discipline on the distinguishing's own carrier you do **not** re-prove its theorems.
You build the carrier and one **faithful readout** onto the borrowed carrier; the discipline then
transports along the readout. The cost of regrounding is the weld, not the corpus.

## 213-native answer

A generated carrier is ℕ₊ read off the distinguishing's successor-spine (`Nat213`:
`theory/math/numbersystems/naturals_from_the_spine.md`). Its **readout** `toNat : Nat213 → Nat` is a
*faithful* map: an injective `+`/`·` homomorphism onto `ℕ₊` that transports `lt`, `le`, and `Dvd`
exactly, both directions (`Lens/.../ToNatReadout.toNat_faithful`). Faithful (injective) + surjective
(onto `ℕ₊`) is precisely what makes the readout a **transport functor**: a statement over `Nat213`
and the corresponding statement over `Nat` are the source- and image-side of one fact
(`theory/essays/synthesis/two_carriers_one_count.md`). So once the weld is built, a result already
proved over native `Nat` is *inherited* over `Nat213` — pulled back along `toNat` — rather than
re-derived.

## Derivation

The weld is realised per operation, and each realisation is the inheritance channel for that
operation's theory. `Valuation.vp_eq_vpSub` makes the generated `p`-adic valuation equal the native
`subMod`-grounded one of the readouts; `Gcd.isGcd_toNat_eq` makes the generated gcd equal the native
`gcdW`; `Congruence.modeq_toNat_iff` makes the generated congruence the native one
(`theory/math/numbertheory/number_theory_over_the_spine.md`). Each is a value-level equation
`generated = native ∘ toNat`, i.e. a commuting square — the defining shape of a transport.

The methodological payoff is concrete. The native corpus already holds the modular headlines —
Fermat, Euler, Wilson over `Nat` (`lean/E213/Lib/Math/NumberTheory/ModArith/`). To have them over
`Nat213` one need not rebuild residue classes and unit groups on the spine; one transports: a native
congruence theorem, read through `modeq_toNat_iff` (reverse), is the `Nat213` statement. The
regrounding workload collapses from *re-derive the field* to *build the weld once per operation, then
inherit*. The descent leg's claim — mathematics as the distinguishing's unfolding — is then not a
demand to re-prove everything natively, but a demand to exhibit the carrier and its faithful readout;
the rest follows by functoriality.

## Dual function

Classically "ℕ₊ ≅ ℕ_{≥1} ⊂ ℕ, so transfer results across the iso" is routine transport of structure.
Strip the set-theoretic packaging that posits two carriers and an isomorphism to be invoked
case-by-case: there is one act (the distinguishing) and one reading of it (`toNat`), and *faithfulness
is the whole content* — it is what lets a proof on either side count as a proof of the one fact. 213
is sharper about the **method**: regrounding is complete when the weld is built (`toNat_faithful` + the
per-operation equations), not when every theorem is re-keyed; "generated, not borrowed" is a property
of the *carrier and its readout*, not of each downstream proof.

## Cross-frame connections

This is the carrier-level instance of main's function-level count-Lens unity: `multiplicativity_is_the
_x_count_lens` and `addition_and_multiplication_are_two_faces_of_one_count` say `vp` is one count-Lens
with two operational faces; `toNat_faithful` says the whole order/divisibility/valuation structure is
one count read at two carrier resolutions. Same functoriality, function-level and carrier-level — the
transport here is the count-Lens applied to the carrier itself (`two_carriers_one_count`).

## Open frontier

Transport has a hard boundary at the carrier's shape, not at the method. Genuinely `0`/sign-valued
objects do **not** pull back to native `Nat213` elements: the count's zero, the empty-product
exponent, and the modular inverse / Bézout coefficient stay readouts into ℕ
(`theory/essays/synthesis/zero_valued_quantities_are_readouts.md`) — `Coprime.coprime_bezout` gives
the coefficients in ℕ, and the full inverse does not lift (no-subtraction, no `−1`). So the inherit-
not-rederive method transports *relations and equalities* freely, but a transported object that is
intrinsically zero-or-signed lands in the readout, not on the spine. A worked `ModArithReadout`
(transporting one native modular theorem — Fermat or Euler — to `Nat213` via `modeq_toNat_iff`) is the
open probe of the method, recorded on the descent-leg frontier.
</content>
