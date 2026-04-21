# 02 — R5's two halves, and the smuggling channel

## Paper 1's R5 in two parts

Paper 1 §3.2 states R5 as:

> **(R5) Reception of infinite structural branches.** Every
> non-terminating structural branch of R must correspond to a
> uniquely determined state in α under the observation rule.
> Combined with R1–R3, the minimal such codomain is `ℝ`.

This conflates two **logically distinct** conditions:

1. **R5a (Distinguishing).** Every Raw term has a unique
   image — `L.view` is injective on Raw.
2. **R5b (Completeness / branch reception).** Every
   *non-terminating structural branch* of Raw (i.e., an
   infinite trajectory, not itself a Raw term) has a unique
   determined state in α.

## R5a: Lean-formalisable, non-trivial

R5a is the `E213.Meta.LensCatalog.Distinguishing` predicate:
```
def Distinguishing {α} (L : Lens α) : Prop :=
  Function.Injective L.view
```
It fails for **swap-blind** Lenses (e.g. `Lens.leaves`,
`Lens.depth`): different Raw terms may share a natural-number
image. So R5a is a genuine constraint that picks out
swap-visible / injective Lenses.

`ziLens` and `z2Lens` (our counterexample Lenses) are easily
checked to be Distinguishing under full injectivity.

## R5b: not formalisable within inductive Raw

R5b quantifies over "non-terminating structural branches".
These are **not** Raw terms:

> "Such branches do not themselves produce R-terms (every
> R-term is finite)." — Paper 1 §3.2

Inductive Raw contains no infinite trees. To state R5b one
has to sit in a coinductive / classical ambient: the
type-theoretic `CoRaw` of potentially-infinite trees, or the
set-theoretic completion of Raw-branches.

Neither is supplied by the 3-clause axiom. Neither is in the
`E213.Firmware.Raw` Lean type.

Within `inductive Raw`, R5b is vacuously true — there is no
element to check. Vacuity is formalised in
`E213.Research.R5Vacuity.foldTotality_vacuous`.

## The smuggling channel

Paper 1 §4.1 derives "α is an ℝ-algebra" from R5:
- R5b forces the codomain to receive uncountably many
  infinite branches (cardinality `𝔠`).
- The minimal Cauchy-complete ordered field of cardinality
  `𝔠` is `ℝ`.
- Hence α ⊇ ℝ, so α is an ℝ-algebra.

**Without R5b**, α needs only to:
- carry a binary combine (R1),
- be a catamorphism target (R2, so combine commutes),
- have no zero divisors (R3),
- have an involution matching swap (R4),
- distinguish Raw terms (R5a).

These constraints do **not** pick ℝ. Countable fields such as
`ℤ[i]`, `ℚ[i]`, `ℤ[√-2]`, and Eisenstein integers all qualify.

## Conclusion

> Removing R5b — the classical-infinity part — collapses
> paper 1's ℂ-uniqueness theorem.

R5a survives in a finitist reformulation and is useful; R5b
is the channel through which classical axioms enter.

Paper 2 will build on this and propose a purely finitist R5
(= R5a) as the authentic 213 reading.
