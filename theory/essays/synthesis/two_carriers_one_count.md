# Two carriers, one count — the depth-readout welds the number theory

The elementary number theory built over the Raw-generated `Nat213` and the same number
theory proven over Lean's native `Nat` are not two disciplines that happen to agree. They
are one count read at two resolutions, and the arrow that welds them is `toNat` — the
depth-readout Lens.

## 213-native answer

`toNat : Nat213 → Nat` is a faithful homomorphism of the whole arithmetic: it preserves
`+` (`Peano.toNat_add`), preserves `×` (`Peano.toNat_mul`), is injective
(`Peano.toNat_injective`), and lands exactly on `ℕ₊` (`Peano.toNat_ge_one`). It is not a
translation between two foreign carriers; it is the distinguishing's *depth* count read out
into ℕ (`theory/math/numbersystems/naturals_from_the_spine.md`: "Lean's `Nat` recovered only
as the `depth` readout, a Lens reading *out*, never the source"). The discipline over
`Nat213` (`theory/math/numbertheory/number_theory_over_the_spine.md`) and the discipline over
native `Nat` (`grounded_fundamental_theorem.md`, `multiplicative_divisor_theory.md`) are the
source-side and readout-side of the **same** statement, and `toNat` is the witness.

## Derivation

A homomorphism that is injective is, in 213, not three concepts (homomorphism / injection /
embedding) but one Lens-arrow read at three argument-patterns — `Lens.refines`
(`theory/lens/unified_equivalence.md`; CLAUDE.md "Equivalence-pluralism"). So `toNat`'s four
properties are one fact: *the count refines without loss*. Preservation of `+`/`×` says the
arrow carries the operations; injectivity says it loses nothing; image `ℕ₊` says native `Nat`
is the readout *plus a zero* the source never had — exactly the `0` that lives in ℕ but not on
the spine (the no-zero shape, `Peano.no_absorbing_element`).

Run a theorem along this arrow. `Nat213`'s `mul_left_cancel` (proved natively from trichotomy,
`number_theory_over_the_spine.md`) and native `Nat`'s cancellation are not two theorems checked
separately; `toNat` carries one to the restriction of the other on `ℕ₊`. `Nat213`'s FTA
(`FTA.fta`) and the grounded FTA over native `Nat` (`grounded_fundamental_theorem.md`,
`factorization_unique`) are the spine-side and readout-side of one factorization fact. The
agreement is the *functoriality of the count-Lens*, not a coincidence to be re-verified per
theorem.

This closes the open frontier of `forced_by_the_distinguishing.md`: the forcing principle's
two scales — the additive count-Lens forced over `Nat213` and the multiplicative `vp`
count-Lens — no longer "run over different carriers." Leg-2 put the multiplicative theory
(`Coprime`, `Gcd`, the `p`-adic `Valuation`) on `Nat213` too, so both scales are now one chain
over one carrier, with `toNat` the readout to the native corpus. The identity-of-form became an
identity-of-source.

## Dual function

Classically this is "ℕ₊ is a sub-semiring of ℕ and the inclusion is a ring map" — true, with
the set-theoretic packaging that posits *two* carriers and then identifies them. Strip it: there
are not two carriers waiting to be glued. There is one act (distinguishing), read at the source
(`Nat213`, the successor-spine) and at its depth count (`Nat`). 213 names *which* arrow welds
them (the depth count-Lens), *why* it is faithful (injective = the distinguishing separates,
the additive twin of `vp_separation`'s multiplicative faithfulness, `seed/AXIOM/06_lens_readings.md`
§6.7), and *what* the readout adds (the `0` the spine forbids).

## Cross-frame connections

`toNat` injective (additive faithfulness) and `vp_separation` (multiplicative faithfulness,
`Meta/Nat/VpSeparation`) are the same demand — a count loses nothing iff its atoms are
distinguishable — at the two scales of `distinguishability_is_the_one_dial.md`. The depth
readout (`toNat`), the leaves readout (`Generation.value_eq_leaves`), and the chart bijection
(`Nat213/Bridge.value_toRaw`) are three presentations of the one count-Lens. And the weld is
itself an instance of the residue's form: the readout `Nat` is the source `Nat213` *plus the
one element it cannot reach* — `0`, the diagonal that no spine-pointing covers
(`seed/AXIOM/06_lens_readings.md` §6.9; the residue `object1_not_surjective` at the level of the
carrier).

## The weld as a proven equation

The carrier weld is not only the homomorphism but a proven *valuation* identity:
`Valuation.vp_eq_vpSub` — for a prime `p` (`p ≠ one`), `vp p n = vpSub p.toNat n.toNat`, the
generated `p`-adic valuation over `Nat213` equals the native `subMod`-grounded `vpSub`
(`Meta/Nat/VpSub213`) of the readouts. The proof is the count-Lens functoriality made concrete:
both valuations are "the largest dividing exponent" (`le_vp_iff` / `le_vpSub_iff`), and the
divisibility carrier bridge `dvd_toNat_iff` (`Dvd a b ⟺ a.toNat ∣ b.toNat`, ⟸ via `toNat`'s
surjectivity onto ℕ₊) with `toNat_powNat` (`(p^k).toNat = p.toNat^k`) matches the two
characterizations, so `Nat.le_antisymm` closes it. The two-scale identity of #103 is now a single
proven equation between the generated and native valuations — the carrier gap, welded in Lean.

## Open frontier

The valuation weld is closed. What remains is breadth: the *same* readout identity for the other
generated operations against their native-corpus counterparts (e.g. a generated `gcd`'s readout
equalling the native gcd), each a small bridge of the `dvd_toNat_iff`/`toNat_*` shape. Tracked
under `the_descent_leg`.
</content>
