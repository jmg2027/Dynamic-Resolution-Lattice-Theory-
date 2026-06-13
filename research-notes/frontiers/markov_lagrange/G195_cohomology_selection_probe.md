# G195 — Direction (#4): the cohomological δ angle on the Markov kernel — a real space-identification, a refuted selection

The speculative shot flagged in `G194` D as the one *local-but-cross-suborbit* candidate that might evade
the locality obstruction: read the realizability selection as a fixed-`c` δ-cohomology condition on the
prime factors.  This note records the attack — a genuine cohomological identification of the root *space*,
and a **machine-checked refutation** of the hope that realizability is a fixed-`c` δ-class.  Discipline:
the positive part is real structure; the negative part is the honest result, with a verified counterexample
(not hand-waving).

## A. The positive structure — windowed roots ≅ `im(δ⁰)` (relative-sign cochains) [SOLID]

At a composite `c = ∏ᵢ pᵢ^{aᵢ}` with ω distinct prime factors (all `≡ 1 mod 4`, so `x² ≡ −1 (mod c)` has
the full `2^ω` solutions), CRT writes a `√(−1)` root as a **sign choice** `s ∈ {±1}^ω`: `x ≡ sᵢ·rᵢ
(mod pᵢ^{aᵢ})`, where `rᵢ` is the fixed windowed `√(−1)` mod `pᵢ^{aᵢ}` (`< pᵢ^{aᵢ}/2`).  So:

  - `2^ω` roots ↔ `{±1}^ω = (ℤ/2)^ω`;
  - the **window** (`x < c/2`) identifies `x` with `c − x = (−s)` — the **global flip** — leaving
    `2^(ω−1)` windowed roots ↔ `(ℤ/2)^ω / ⟨(1,…,1)⟩`.

Now read the ω prime factors as **vertices** and apply the repo's simplicial coboundary
(`Cohomology/Delta/Core`, ℤ/2): `δ⁰ : C⁰ → C¹` sends a vertex-cochain `s` to the edge-cochain
`(sᵢ ⊕ sⱼ)`.  Then:

  - `ker δ⁰ = {constant cochains} = ⟨(1,…,1)⟩` = **exactly the global flip** the window kills;
  - so the windowed roots `≅ (ℤ/2)^ω / ker δ⁰ = im(δ⁰)` — the **relative-sign cochains** (the `sᵢ ⊕ sⱼ`
    edge data).

This is a clean, true cohomological identification: **a windowed `√(−1)` root is precisely a relative-sign
class on the prime-vertex graph (an `im δ⁰` element); the window quotient is `H⁰`'s kernel**.  It is
*local in `c`* (it lives entirely in `c`'s CRT data) yet *cross-suborbit* (it organises all `2^(ω−1)`
competitors at once) — which is why it was the candidate to evade the `G194` locality obstruction.

## B. The negative result — realizability is NOT a fixed-`c` δ-class [MACHINE-CHECKED]

The hope: the *realized* windowed root is a distinguished δ-class (e.g. always the "opposite" edge `= 1`).
Tested against three `ω = 2` cases (each realized root identified from its actual Markov triple), reading
the relative sign `sᵢ ⊕ sⱼ` (`= +` iff `u ≡ rᵢ` on factor `i`):

| `c` | factor | realized root (triple) | `(s₁, s₂)` vs windowed reps | `δ⁰`-edge |
|---|---|---|---|---|
| `985` | `5·197` | `408` (`(2,169,985)`) | `(−r₅, +r₁₉₇)` (`408%5=3≠2`, `408%197=14`) | `1` (opposite) |
| `1325` | `25·53` | `507` (`(13,34,1325)`) | `(+r₂₅, −r₅₃)` (`507%25=7`, `507%53=30≠23`) | `1` (opposite) |
| `4181` | `37·113` | `1597` (`(1,1597,4181)`) | `(+r₃₇, +r₁₁₃)` (`1597%37=6`, `1597%113=15`) | `0` (**same**) |

The two deep cases (`985`, `1325`) give edge `1`; the **Fibonacci-spine** case `4181 = F₁₉`, triple
`(1, 1597, 4181)` with the trivial partner `b = 1`, gives edge `0` — **breaking** the "realized = opposite"
pattern.  Machine-checked as `realized_root_relative_sign_not_uniform` (`SternBrocotMarkov`, ∅-axiom):

```lean
((decide (408 % 5 = 2) == decide (408 % 197 = 14))
   == (decide (1597 % 37 = 6) == decide (1597 % 113 = 15))) = false
```

(`985`'s relative-sign Bool `≠` `4181`'s).  So **realizability is not a fixed-`c` cohomological condition
on the primes**: the `δ⁰`-edge of the realized root is *not* a uniform invariant.

## C. Verdict — the cohomology structures the space, the selection stays global

Direction #4 delivers a real structural payoff (A: the windowed-root space *is* `im δ⁰`, a genuine
cohomological identification, ∅-axiom-able) but **does not evade the locality obstruction** for the
selection (B).  The reason matches `G194`: the realized δ⁰-edge depends on the *global tree position*
(`4181` on the Fibonacci spine, partner `b = 1`, vs `985`/`1325` deep with large partners) — not on any
fixed-`c` datum.  The selection is global; the prime-vertex δ-cohomology sees only the local CRT data and
so cannot pick the class.

What would still be worth building (positive residue):
  - the **general ∅-axiom `windowed roots ≅ im δ⁰`** identification (currently only the concrete
    counterexample is formalised) — a real cohomological structuring of the `SqrtUnity` torsor, valuable
    independent of `H`;
  - a δ on the **tree** (Vieta-adjacency) rather than the **primes** — the obstruction says the selecting
    structure is cross-`c`/global, so a *tree-indexed* cochain complex (if the realized signs form a
    cocycle across Vieta-adjacent triples) is the version that could carry `H`.  This re-imports the
    cross-`c` character (and so meets the same wall the continuant/stable-norm route meets), but is the
    honest place the cohomological idea would have to live.

## D. Net across directions 1–4 (standing)

Every attack converges: **structure fully pinned (count, group, free action, window, even the
cohomological space-identification), selection is the sole open freedom, and the selection is global in
`c`.**  The local routes (forcing #2, prime-δ #4) provably cannot select; the cross-`c` routes (continuant
#1, stable norm, tree-δ) are where `H` lives — all necessary-not-sufficient at the proven frontier
(Aigner).  Recorded down-payments this branch: §34 iff (= Frobenius), `Real213/ContinuedFraction/Continuant` (E1),
`MarkovMaxUnique 985`, the relative-sign counterexample — plus the obstruction map (`G192`/`G194`) and the
attack map (`G193`).

### Pointers
- counterexample: `Real213/Markov/SternBrocotMarkov.realized_root_relative_sign_not_uniform`
- δ apparatus: `Cohomology/{Delta,Cochain}/Core` (ℤ/2, `δ²=0`)
- companions: `G194` (locality obstruction), `G193` (axiom attack map), `G192` (Raw/Lens boundary), `G191` (continuant)
