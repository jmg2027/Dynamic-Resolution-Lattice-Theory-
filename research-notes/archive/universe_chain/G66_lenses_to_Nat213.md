# G66: Lenses Raw → Nat213 — characterization

## User question (2026-05-09)

> "Nat213을 만드는 렌즈가 무한히 많은가, 둘 이상이라면 그 렌즈들은
> 어떤 공통점과 차이점들을 가지고 있느냐"
>
> "Raw 타입 자체 생성자도 어찌보면 렌즈지만… 일단 렌즈라고 안치고
> 항등렌즈로 퉁치자구"

## Setup

Treat `Raw` constructor (`slash`, `a`, `b`) as the "identity lens"
(structural primitive).  Investigate non-identity lenses
`Raw → Nat213` — i.e., catamorphisms / fold-based functions that
project Raw structure into Nat213 (positive naturals).

## Definition: a Lens to Nat213

A **Nat213-lens** = `Raw → Nat213` defined via `Raw.fold` with
parameters:
- `base_a : Nat213` (image of `Raw.a`)
- `base_b : Nat213` (image of `Raw.b`)
- `combine : Nat213 → Nat213 → Nat213` (image of `slash`)

By Raw.fold's catamorphism property, this uniquely defines a
function on all of Raw.

## Forced constraint: both atoms must contribute

Since `Nat213` has no zero element, `base_a, base_b ∈ Nat213` are
both ≥ 1.  Therefore:

> **Every Nat213-lens forces both atoms (a and b) to contribute
> non-trivially.  No lens can "ignore" one atom.**

This is **structurally distinct** from Nat-with-0 lenses, where
`base_a = 0` would let you "count only b-atoms".  In 213-native
counting, BOTH sides matter.

## Infinitude of Nat213-lenses

For any pair `(ba, bb) ∈ Nat213²` and any closed combine
`+ : Nat213 → Nat213 → Nat213`, fold yields a distinct Nat213-lens:

| (ba, bb) | combine | Resulting lens |
|---|---|---|
| (1, 1) | + | leaf count (= total atoms) |
| (2, 1) | + | weighted: a counts 2, b counts 1 |
| (1, 2) | + | weighted: a counts 1, b counts 2 |
| (1, 1) | · | product of atom counts |
| (2, 2) | + | 2× leaf count |
| (n, m) | + (any n, m ∈ ℕ_+) | infinitely many |

So **at least countably infinitely many Nat213-lenses exist**.

## Common features of all Nat213-lenses

All fold-based lenses share:

### Common Feature 1: Catamorphism property
Every Nat213-lens `L = fold ba bb combine` satisfies:
- `L (Raw.a) = ba`
- `L (Raw.b) = bb`
- `L (slash x y) = combine (L x) (L y)`

This is the **universal property of fold** — every lens is uniquely
determined by `(ba, bb, combine)`.

### Common Feature 2: Both atoms ≥ 1
Forced by Nat213's structure (no 0).

### Common Feature 3: Image is in Nat213 (≥ 1)
Result is always positive — no Raw maps to "0".

### Common Feature 4: Monotonicity (for combine = +)
If combine is + (or any monotone op): adding more structure
(deeper Raw) produces larger output.

## Differences between lenses

| Aspect | Variable across lenses |
|---|---|
| Atom weights `(ba, bb)` | parametrize the lens |
| Combine operation | `+`, `·`, `max`, `min`, etc. |
| Resulting "interpretation" | count, weight, depth-like, etc. |
| Sensitivity to balance | (ba, bb) determines a/b balance |
| Sensitivity to depth | combine determines depth-folding |

## Equivalence classes

Two lenses `L₁, L₂` are **observationally equivalent** if
`∀ r, L₁ r = L₂ r`.  By fold uniqueness:

> Lenses are observationally equivalent iff they have the same
> `(ba, bb, combine)` triple (up to algebra-isomorphism of the
> codomain).

So the **classification of Nat213-lenses** = equivalence classes
of `(ba, bb, combine) ∈ Nat213² × (Nat213 → Nat213 → Nat213)`.

## Open questions

1. Is the classification countable or uncountable?  Depends on
   whether `Nat213 → Nat213 → Nat213` is countably or
   uncountably many functions.  If we restrict to "computable"
   or "definable" combines, countable.
2. Are there "natural" lenses (preferred by 213 axiom)?  Probably
   `(1, 1, +)` (leaf count) is most natural.
3. Do orthogonal-axis quotients (G62) factor through specific
   Nat213-lenses?  E.g., `npairToInt` is `(L_a r) - (L_b r)` where
   L_a, L_b are atom-specific counts.  But these aren't Nat213-
   lenses (their image is ℤ).
4. What's the relation to Raw's swap automorphism?  A lens is
   **swap-invariant** iff `ba = bb` (else swap changes output).
   This gives a special sub-class.

## Lean formalization plan

1. Define `Nat213Lens` = structure `(ba bb : Nat213) (combine :
   Nat213 → Nat213 → Nat213)` + the fold function as observable.
2. Show two specific lenses give different outputs on some Raw.
3. Show there's an infinite family (parametrized by ℕ_+ × ℕ_+).
4. Show swap-invariant lenses = those with ba = bb.

## See also

- `lean/E213/Theory/Raw/Fold.lean` — Raw.fold catamorphism
- `lean/E213/Theory/Nat213/Core.lean` — Nat213 type
- `research-notes/G65_nat213_proper_type_synthesis.md` — Nat213 motivation

## Update: equivalence vs difference (formal)

Reformulation per user clarification (2026-05-09):

> "Raw 타입에 항등렌즈를 씌우고 그걸 세는걸 자연수라고 정의했을 때,
> 다른 렌즈들에서 이게 똑같이 나오느냐"

The question is about whether **different lenses produce the SAME
or DIFFERENT** values when applied to the same Raw.

### Formal answer: GENERALLY DIFFERENT

| Pair of lenses | Same output? | Witness |
|---|---|---|
| `lensLeafCount` vs `lensWeighted21` | NO | `Raw.a`: 1 vs 2 |
| `lensWeighted21` vs `lensWeighted12` | NO | `Raw.a`: 2 vs 1 |
| `lensLeafCount` vs `lensProduct` | NO | `slash a b`: 2 vs 1 |
| Same (ba, bb, combine) | YES | catamorphism uniqueness |

### What IS preserved across all Nat213-lenses

1. **Atomic image determined by (ba, bb)**: regardless of combine,
   `L Raw.a = ba` and `L Raw.b = bb`.
2. **Image always ≥ 1**: every value lies in Nat213.
3. **Catamorphism structure**: `L (slash x y) = combine (L x) (L y)`.
4. **No-zero-image**: no Raw maps to 0 (since 0 ∉ Nat213).

### What VARIES across lenses

1. Atomic weights (ba, bb)
2. Combination operation (+, ·, max, min, ...)
3. Resulting interpretation (count, product, weighted, depth-like)
4. Sub-monoid of Nat213 produced as image

### Lean ∅-axiom witnesses (this update)

Added 5 more theorems to `Theory/Nat213/Lenses.lean`:
- `weighted_lenses_differ_on_atom` — (2,1,+) ≠ (1,2,+) on Raw.a
- `add_vs_mul_differ_on_compound` — `+` ≠ `·` on slash a b
- `lenses_not_all_equivalent` — ∃ Raw where outputs differ
- `atom_value_independent_of_combine` — atom values ⊥ combine
- `same_params_same_output` — catamorphism uniqueness

Total 11 ∅-axiom theorems on Nat213-lens characterization.

### Conclusion

**다른 lens들은 같은 값을 안 줌** (in general).  Only when the
parameter triple `(ba, bb, combine)` matches do two lenses agree
everywhere.

But ALL Nat213-lenses share:
- Catamorphism property
- Both-atom-positive constraint (forced by Nat213's no-zero design)
- Image ⊆ Nat213 (≥ 1)

So the **structural shape** of "Nat213-counting" is invariant
(determined by Raw's catamorphism + Nat213's no-zero), while the
**specific numerical values** depend on the lens choice.

This is a meaningful answer to the user's question: lenses are
NOT all equivalent at the value level, but they all share the
same structural skeleton dictated by Raw + Nat213.
