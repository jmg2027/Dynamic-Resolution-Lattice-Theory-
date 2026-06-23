# GRA universality — one principle, five readings

## Triggering question

> "The walk-length of a graph, the cup-length of cohomology, the truncation
>  of HoTT, the chromatic height of an operad, the resolution exponent of
>  analysis — why are these the same thing?  What does 'the same' mean?"

## 213-native answer

A single arithmetic — additive accumulation of two coprime grades
`(g₁, g₂) = (NT, NS) = (2, 3)` — is what each of the five Readings
reads.  The Readings are not "analogous" or "isomorphic-up-to-
philosophy"; they are five surface presentations of the same
syntactic object, the `(2,3)`-GRA model, and the sameness is a
typeclass instance witness in `lean/E213/Lib/Math/Algebra/GRA/`.

The "killer app" of this view — translation theorems — follows
mechanically: any property `P` of the depth function `⌈n/3⌉`
proved in one Reading transports to all five, with no need to
chase coincidences across domains.

## Derivation

### §1 The arithmetic

`GRAModel` (`lean/E213/Lib/Math/Algebra/GRA/GRAModel.lean`) is the
7-axiom typeclass:

| Axiom | Content |
|---|---|
| A1 | `gen1 < gen2`, `gcd(gen1, gen2) = 1` |
| A2 | `grade(a ⊕ b) = grade(a) + grade(b)` |
| A3 | `grade(a ⊗ b) ≤ grade(a) + grade(b)` |
| A4 | `∀ n ≥ gen1, ∃ a b. n = gen1·a + gen2·b` |
| A5 | `depth(n) = n / gen2 + (n % gen2 ≠ 0)` |
| A6 | `depth(n) = ⌈n / gen2⌉` |
| A7 | (Lens universality — discharged by the five `GRA23_*` instances) |

The specialization `(gen1, gen2) = (2, 3)` is `GRA23Model`.  The
data is `Nat`; the meaning is "how many uses of the small primitive
and how many of the large primitive build a grade-`n` element."

### §2 The five Readings

| Reading | File | Carrier reading | gen1 = 2 | gen2 = 3 |
|---|---|---|---|---|
| R₁ Cohomology | `GRA/Cohomology.lean` | cochain degree | edge-cochain on K_{3,2} | face-cochain on Δ⁴ |
| R₂ Higher Algebra | `GRA/HigherAlgebra.lean` | E_n operad level | E₂ binary | E₃ ternary |
| R₃ HoTT | `GRA/HoTT.lean` | truncation level | 2-truncation | 3-truncation |
| R₄ Graph | `GRA/Graph.lean` | walk length | K_{3,2} 2-step cycle | K_{3,2} 3-step path |
| R₅ Analysis | `GRA/Analysis.lean` | resolution exponent | binary cut-double | ternary cut-triple |

The hub is `GRA/NumberTheory.lean`: `Nat` itself as a (2,3)-GRA
model.  Each Reading produces an iso `GRAIso R_i NT` (refl/symm/trans
are `GRAIso.refl/symm/trans` in `GRAModel.lean`), so the
universality capstone `gra_universality_witness`
(`GRA/HigherAlgebra.lean`) is hub-and-spoke transitivity, not
ten separate iso proofs.

### §3 The translation theorem is the dual function

`graph_distance_implies_cup_length`
(`GRA/Translation.lean`): for every `n ≥ 2`,

  `Graph.graphDepth n = Cohomology.cohomDepth n`.

The left side is the minimum walk-length needed to traverse a
grade-`n` element in `K_{3,2}`; the right side is the minimum
cup-length needed to build a degree-`n` cochain from the primitive
generators.  The equality is `rfl`-after-`simp` once both sides
reduce to `(n + 2) / 3` — they are not "compared"; they are
already the same expression.

The master form is `master_translation_from_any`
(`GRA/Translation.lean`):

  `∀ P : Nat → Prop, P ((n+2)/3) → P (Graph.graphDepth n) ∧
   P (Cohomology.cohomDepth n) ∧ P (Analysis.analysisDepth n) ∧
   P (HoTT.hottDepth n) ∧ P (HigherAlgebra.haDepth n)`.

A single property `P` is established once, against the universal
depth `⌈n/3⌉`; the five Reading-specific statements fall out
automatically.

### §4 The universal prediction

`universal_depth_comparison` (`GRA/Translation.lean`):

  `∀ n ≥ 2, (n + 2) / 3 ≤ (n + 1) / 2`.

The greedy algorithm on gen2 = 3 is always at least as efficient
as the naive algorithm on gen1 = 2.  This is simultaneously:

| Reading | Prediction |
|---|---|
| Graph | A walk decomposition prefers 3-step paths over 2-step cycles |
| Cohomology | A cup factorization prefers degree-3 generators over degree-2 |
| HoTT | A homotopy resolution prefers 3-truncations over 2-truncations |
| Analysis | A resolution shift prefers ternary cuts over binary cuts |
| Higher Algebra | A chromatic height bound prefers E₃ towers over E₂ towers |

One omega proof, five Reading-specific corollaries: `graph_depth_le_naive`,
`cohom_depth_le_naive`, `analysis_depth_le_naive`, `hott_depth_le_naive`,
`ha_depth_le_naive`, all in `GRA/Translation.lean`.

## Dual function

Read classically, the theorem says "the same combinatorial bound
appears in five different mathematical fields."  Read 213-natively,
the redundancy is gone: the five fields were never separate
arithmetics, they were five Readings of one arithmetic, and the
"five" is a Lens artifact of which surface presentation a reader
arrives through.  `gcd(2,3) = 1` (Frobenius = 1 for the (2,3) pair)
forces universal reachability for `n ≥ 2`; that forcing is the same
event no matter which field's vocabulary names it.

## Cross-frame connections

The (2,3)-GRA structure rhymes with three other 213 facts and is
not a separate phenomenon:

  · **det(P) = 1** (`theory/math/algebra/mobius213_p_orbit_closure.md` —
    P = [[2,1],[1,1]]).  Same NS = 3, NT = 2 from the same
    self-form fixed point.
  · **Frobenius = 1 for (2, 3)** (Chicken McNugget specialization):
    the largest non-representable integer is 1.  This is the
    reason A4 reads "every `n ≥ gen1`" rather than "every
    `n ≥ some threshold > gen1`."
  · **K_{3,2}^{(c=2)} closure form**
    (`rust-engine/docs/closure-algorithm.md`): observables factor
    as `R(NS, NT, d, c) · Π (1 + κ · αⁿ)`.  The exponent `n` in
    that product is a GRA depth — the bipartite-graph reading R₄
    of the cohomological reading R₁ both meet at the same
    integer `n`.

Five Readings + det = 1 + Frobenius = 1 + closure form = same
syntactic fact at four resolutions.

## Open frontier

The current iso proofs are at the simplified carrier `Nat = grade`.
The full content of the GRA universality conjecture is that the
isos lift to actual Walk objects, Cochain complexes, n-truncated
types, and operad algebras — at which point the iso is a
non-trivial functor rather than the identity map on `Nat`.  This
is the categorical-enrichment programme, deliberately deferred so the
five-Reading skeleton would compile and the translation theorems
would land first.  The depth-level universality is closed; the
carrier-level universality is the open research front.

The narrative chapter `theory/math/algebra/gra_book.md` Ch. 7 lists the
formalization gaps that would close at carrier enrichment; the
Lean iso witnesses already pin down the depth-level statement, so
no further omega-on-Nat work is needed to keep the present claim.

## Self-check note

The first draft of this essay started with "Langlands-style
translation between mathematical domains."  That is the wrong
frame: it imports a comparison ("Langlands transfers BETWEEN
fields") when the (2,3)-GRA reading is precisely that the fields
were not separated to begin with.  Retreat in place: the
translation theorem is not a bridge across domains, it is the
witness that the alleged domains coincide on the relevant
arithmetic.  The Lean statement
`graph_distance_implies_cup_length n hn : Graph.graphDepth n =
Cohomology.cohomDepth n` is one equation, not a translation
procedure.
