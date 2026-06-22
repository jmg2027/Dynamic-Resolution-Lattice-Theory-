# Forced by the distinguishing — one forcing principle at two scales

A quantity or structure is **forced by the distinguishing** when it is the *unique* readout the act
of distinguishing determines: fix how the act is read on the atoms and on a pairing, and the whole
readout is pinned — and *remove* the distinguishing (collapse the separating axis) and the structure
collapses with it. The same principle reads at the foundation (the count, the residue) and in
multiplicative number theory (multiplicativity, the prime-valuation vector); they are one principle,
not an analogy.

## 213-native answer

"Forced" has a precise operational shape with two halves, both about a *distinguishing axis*:
**uniqueness** (a reading consistent with the act is the *only* one) and **necessity** (a reading
*blind* to the act collapses). At the foundation this is
`Lens/Number/Nat213/Generation.count_reading_forced`: any `g : Raw → Nat` sending each atom to `1`
and a `slash` to `+` is *identically* the leaf-count — initiality (`Lens.view_unique`) leaves no
freedom. Its necessity twin is `Generation.distinguishing_necessary`: a distinguishing-*blind*
combine (`fun _ _ => 1`, ignoring the `slash`) sends every numeral to one value, so it cannot tell
`numeral 0` from `numeral 1`, while the `+`-reading separates them. And on the value side,
`OneDiagonal.residue_needs_distinguishing`: on a subsingleton value-space (no distinction) every
modifier has a fixed point, so the residue diagonal does not even exist. Forced ⟺ uses a separating
distinguishing axis; remove it ⟹ collapse.

## Derivation

Multiplicative number theory states the *same* two halves over a *different* distinguishing axis.
`theory/essays/synthesis/the_forcing_criterion_is_distinguishing.md` pins the criterion verbatim: a
quantity is forced ⟺ it names a genuine distinguishing axis; **faithful** ⟺ the axes separate
(`Meta/Nat/VpSeparation.vp_separation` — a positive natural is determined by its prime-valuation
vector); **removable** ⟺ no axis added. And
`theory/essays/synthesis/multiplicativity_is_the_x_count_lens.md`: a function is multiplicative ⟺ it
is a readout of the **×-count-Lens** (the prime-exponent vector `vp`), faithful by `vp_separation`,
factoring through the per-prime-power axes.

The two scales are one principle because they are the *same act read on two count-Lenses*. At the
additive scale the atoms are `a, b` and the count is leaves (`Generation.leaves_numeral`); the reading
is forced because `slash` separates (`distinguishing_necessary`). At the multiplicative scale the
atoms are the **primes** — the ×-atoms — and the count is `vp`; multiplicativity is forced because the
primes separate (`vp_separation`). The necessity half transfers exactly: multiplicativity *exists*
because ×-atoms are **distinguishable** where +-atoms (units) are **not**
(`Meta/Nat/UnitList.append_comm` — the units commute/collapse, drawing no distinction). So
`distinguishing_necessary` (a distinction-blind combine collapses the count) *is* "units don't
distinguish, so the additive unit-count carries no multiplicative information" — the same collapse,
one scale up. `vp_separation` is `count_reading_forced`'s faithfulness at the ×-atom resolution.

## Dual function

Read classically these look like two unrelated facts: "the leaf-count catamorphism is the unique
homomorphism" (a free-algebra triviality) and "the fundamental theorem of arithmetic makes
multiplicative functions well-defined" (number theory). Stripping the packaging, both are the single
statement *the count is forced exactly when its distinguishing axis is faithful (separates), and
collapses exactly when it is not*. 213's reading is sharper than either classical statement because it
names the one thing they share — a separating distinguishing axis — and shows initiality (additive)
and the FTA (multiplicative) to be its two instances, not two theorems that happen to rhyme.

## Cross-frame connections

`count_reading_forced` (Lens initiality, additive count) + `vp_separation` (FTA, multiplicative count)
+ `distinguishing_necessary` / `residue_needs_distinguishing` (collapse under no-distinction) +
`UnitList.append_comm` (the +-atoms that *don't* distinguish) are one fact at additive-count and
multiplicative-count resolutions: a readout is forced ⟺ its atoms distinguish, and the residue/the
count is precisely what that distinguishing leaves.

## Open frontier

The identity is currently an identity-of-form across two carriers: the foundational half runs over
`Nat213` (the Raw-generated naturals), while `vp`/`vp_separation` run over Lean's native `Nat`. Wiring
multiplicative number theory over `Nat213` (the descent leg's leg-2 depth) would turn the two-scale
identity from a proven *analogy* into a single proven *chain* — the multiplicative count-Lens read off
the same distinguishing the additive one is. Tracked under `the_descent_leg`.
