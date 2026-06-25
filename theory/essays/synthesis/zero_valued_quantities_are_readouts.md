# Zero-valued quantities are readouts, not elements

Over the Raw-generated `Nat213` a quantity that can be **zero or signed** — a multiplicity, an
exponent, a Bézout coefficient — is never a `Nat213` element. It is read *out* into ℕ, the
count-Lens direction. The carrier's no-zero shape forces it, and the forcing is the content.

## 213-native answer

`Nat213` is ℕ₊ read off the distinguishing's successor-spine: `one := Raw.a`, `succ := slashOrSelf ·
Raw.b`, with no zero and no closed subtraction — the shape is *proven*, not stipulated
(`Peano.no_absorbing_element`, `add_ne_self`; `theory/math/numbersystems/naturals_from_the_spine.md`).
So when a construction needs a value that is `0` (an absent count) or signed (a difference), that value
**cannot be an element of the carrier**. It lands instead in the readout ℕ — the same legitimate
"reading-out" direction by which `toNat`/`depth` recover Lean's `Nat` from the spine
(`theory/essays/synthesis/two_carriers_one_count.md`). Three constructions hit this, identically.

## Derivation

**Valuation.** A `p`-adic valuation counts how many times `p` divides, and that count can be `0` (when
`p ∤ n`). So `vp : Nat213 → Nat213 → Nat` returns a *native* `Nat`, not a `Nat213`
(`theory/math/numbertheory/number_theory_over_the_spine.md`, `Lens/.../Valuation.vp`). To even write
`p^(vp p n)` the exponent power must accept a zero exponent, which `pow` (whose exponent is a `Nat213`,
hence ≥ 1) cannot — so `Peano.powNat` is introduced precisely to provide `powNat a 0 = one`. The count
reads out; the carrier supplies only the divisor, which stays native (`pow_vp_dvd`).

**Exponent.** The same `powNat a 0 = one` is the empty product — the multiplicative `0`. `pow`
generates the ≥ 1 powers from the spine; `powNat` is its extension to the readout exponent
(`pow_eq_powNat_toNat : pow a m = powNat a (toNat m)`). The zero lives only on the ℕ side.

**Bézout / inverse.** `Coprime.coprime_bezout` gives, for `Coprime a m`, native coefficients
`∃ x y : Nat, a.toNat·x = m.toNat·y + 1 ∨ m.toNat·y = a.toNat·x + 1` — read out through the carrier
weld (`isGcd_toNat_eq` reads `Coprime` onto `gcdW = 1`, then `SubBezout213.bezout_one_of_coprime`).
The coefficients are in ℕ because a Bézout coefficient may be `0`, and the inverse is *signed*. The
full native element `∃ x : Nat213, a·x ≡ 1 (mod m)` does **not** lift: the second Bézout branch needs a
`−1`/`m − 1` complement the no-subtraction carrier cannot build (`frontiers/the_descent_leg.md`,
"No-zero friction").

The three are one principle: **a quantity whose natural range includes `0` or a sign is a reading of
the distinguishing, not one of its acts.** The acts (atoms, successors, products) are the `Nat213`
elements; `0` and the negative are pre-Lens — they belong to the residue the readout names, not to the
spine.

## Dual function

Classically one says "ℕ₊ is missing `0`, so embed it in `ℕ` (or `ℤ`) and work there." Strip the
embedding-as-repair framing: there is no defect to repair. The valuation, the exponent's zero, and the
inverse's sign are *counts and differences* — and a count is what a count-Lens **hands back**, read
out, never an element it reads (`naturals_from_the_spine.md`: `Nat` recovered as the `depth` readout,
"a Lens reading *out*, never the source"). 213 is sharper here: it says *which* quantities must be
readouts (the `0`/sign-valued ones) and *why* (the carrier has no act for `0`), turning "ℕ₊ lacks
zero" from a deficiency into a diagnostic — the readout marks exactly where the generated object
departs from `ℤ`/`ℕ`-with-zero.

## Cross-frame connections

`0` is not an element waiting to be added: `seed/AXIOM/06_lens_readings.md` §6.5 reads the point `≡ K_∞
≡ ∞`, and §6.9 fixes `0` and `∞` as **one pre-Lens residue**, a Lens-artifact, never a stratum-value
(the CLAUDE.md failure-mode row "0/∞ as a stratum-value"). The valuation no-zero decision, the
`powNat 0` empty product, and the un-liftable signed inverse are the *same* fact at three resolutions:
each is a place where a reading wants `0`/sign, and the carrier — having no exterior dialer for it
(§5.1) — answers by reading out rather than admitting an element. Same fact as the count-Lens doctrine
(`two_carriers_one_count.md`): `Nat213` *is* `ℕ₊`, and `ℕ`'s extra `0` is exactly the readout's degree
of freedom.

## Open frontier

The full modular inverse as a native `Nat213` object (and the dual `lcm` join) stay unbuilt — not for
lack of machinery but because the no-zero shape makes them readouts by nature; `frontiers/the_descent_leg.md`
records the obstruction as a carrier characteristic, not a gap.
</content>
