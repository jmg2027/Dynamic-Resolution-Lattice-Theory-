# What a natural number counts

A natural number is not a primitive in 213 — it is **what a count-Lens hands back**
when pointed at the distinguishing. The distinguishing admits more than one count-Lens,
so the honest question is not "what is ℕ" but "which counting, of which distinguishing."

## 213-native answer

The first distinguishing yields two atoms `a, b`; iterating one `slash`-operation from
a seed generates structure, and a **count-Lens** reads a `Nat` off that structure. ℕ is
the readout, not the source (`seed/AXIOM/06_lens_readings.md` §6.7, "ℕ is what the
count-Lens hands back"). Two such readouts are isomorphic to ℕ; a third counts something
else entirely. "Which natural number" is fixed by which distinguishing you count.

## Derivation — three count-Lenses on one distinguishing

**Multiplicity.** Take `List Unit` — lists of indistinguishable units — and read
`count : List Unit → Nat`. Append is the primitive combine, and `count` is its
homomorphism (`count (l ++ m) = count l + count m`); the whole ordered commutative
semiring `(ℕ, +, ·, 0, 1, ≤)` is the count-shadow of unit-list operations, each law's
proof verified free of the ℕ-law it produces (`theory/math/numbersystems/arithmetic_generation.md`).
Here ℕ is *how many units*; `+` is born from append.

**Depth.** Take instead the `slash`-successor `rawSucc r := slashOrSelf Raw.a r` and its
closure `IsRawNat` from the seed `b`, and read `toNat x := x.val.depth`. The successor
fires as `a / r` (`a ≠ r` for every closure element), raising depth by exactly one
(`rawSucc_depth`), so `toNat` is a Peano isomorphism `RawNat ≃ ℕ`
(`theory/math/numbersystems/naturals_from_the_spine.md`). Here ℕ is *how deep* the
self-pointing tower goes; `succ` is first, `+` is iterated `succ`.

These two are the *same* ℕ at different resolutions — multiplicity reads append, depth
reads the successor — agreeing rung for rung. The natural-number object is recovered
either way; neither is privileged.

**Population.** Read the *same* spine a third way: `census x := rawCount (toNat x)`,
where `rawCount n = 2 + C(rawCount (n−1), 2)` counts the distinct `Raw`s of depth ≤ n —
the sequence `2, 3, 5, 12, 68, …` (`RawNatCensus`, `Lib/.../UniverseChain/RawRecurrence`).
At the depth-2 rung the linear reading hands back `2` while the population reading hands
back `5` (`two_readings`). This is not a third copy of ℕ — it is a count-Lens on the
spine that hands back the level-cardinality, a strictly faster reading of the one object.

## Dual function

This is the natural number with its packaging stripped: not an axiomatized Peano set
assumed at the foundation, but the value a counting returns — `toNat x = x.val.depth` is
a `Raw`'s depth, `count l` is a list's length, `census x` is a population. The refinement
213 adds is that *the counting is not unique*: where the classical natural number is one
object, here it is the agreement-class of those count-Lenses that happen to be Peano
isomorphisms (multiplicity, depth), with other count-Lenses on the same distinguishing
(population) handing back different numbers. "5 things of depth ≤ 2" and "the number 2"
are two countings of one rung.

## Cross-frame connections

The same spine carries the linear (`toNat`) and the population (`census`) readings
(`two_readings`); the same distinguishing carries the multiplicity (`count`) reading.
The divergence is exactly *what gets counted*: units (multiplicity), levels (depth), or
inhabitants-per-level (population). The forcing that makes any of these generative is one
layer below — binary-distinct is the unique generative primitive
(`RivalArity.arity_distinctness_forcing`): a unary primitive counts a line, a
`Bool`-valued relation counts at most two classes, only the binary `slash` with
distinctness branches into a counted population at all.

## Open frontier

That the carrier `IsRawNat` and the readout `Nat` rest on the kernel's `inductive`
mechanism is the conceded boundary — the distinguishing *is* an inductive act; the count
is read *out* into `Nat`, the legitimate direction, but not eliminated
(`theory/math/numbersystems/naturals_from_the_spine.md`, open frontier).

## Self-check note

The seed framing said "ℕ generated three ways." That overcounts: only two readings
(multiplicity, depth) *are* ℕ — isomorphic Peano objects. The population reading counts
the same spine but hands back a different sequence, so it is a third *count-Lens on the
distinguishing*, not a third ℕ. The honest claim is three countings, two of which
coincide as the natural-number object.
