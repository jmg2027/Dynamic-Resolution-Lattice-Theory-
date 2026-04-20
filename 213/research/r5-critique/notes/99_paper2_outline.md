# Paper 2 outline (draft)

**Working title:** *The ℝ-algebra assumption in 213 — a
finitist critique*

**Relation to Paper 1:** adversarial / companion.  Paper 1
presents the mainstream-looking ℂ-uniqueness theorem; this
paper dissects it.

## 1. Recap

Paper 1's axiom → R1–R5 → ℂ uniqueness chain, in one page.

## 2. The two halves of R5

- **R5a (Distinguishing):** `L.view` is injective. Lean:
  `E213.Meta.LensCatalog.Distinguishing`.
- **R5b (Infinite-branch completeness):** every
  non-terminating structural trajectory corresponds to a
  unique codomain state.

Claim: R5b is the sole source of "codomain is an ℝ-algebra"
in Paper 1 §4.1.

## 3. R5b is classical infinity

Inside inductive Raw, no "non-terminating trajectory" exists.
R5b's universal quantifier is either vacuous (over ∅) or
imports an external coinductive / set-theoretic ambient.
Lean: `E213.Research.R5Vacuity.foldTotality_vacuous`.

## 4. Counterexamples under R1–R4 alone

Two explicit countable witnesses:
- **ZI** = ℤ[i], Gaussian integers.
- **Z2** = ℤ[√-2].

Both satisfy R1–R4; all Lean-verified modulo the
`Raw.fold_swap_hom` firmware helper.

## 5. Consequences

- ℂ-uniqueness theorem holds **only** in the classical-infinity
  frame supplied by R5b.
- Under finitist R5 = R5a, the class of admissible codomains
  is a **spectrum** parameterised by base field.
- Paper 1's "ℂ" is thus the **physically relevant** Lens, not
  the unique mathematical Lens.

## 6. Finitist reformulation (proposed)

Axiom + R1–R4 + R5a = 213's true mathematical content.
ℂ's specialness (if any) must come from elsewhere — e.g.,
categorical universal property, or physical / geometric
input.

## 7. Open questions

- Is there a 213-internal condition (not R5b) that restores
  ℂ uniqueness?  See `03_e4_restoring_c.md`.
- What is the full classification of R1–R4 Lenses? (E5)
- Relation to Stone duality / motivic Galois theory?

## 8. Philosophical stance

213 is pre-mathematical.  Mathematics emerges from Lens
choices.  The spectrum of Lenses **is** the spectrum of
mathematics.  ℂ is not an internal necessity; it is a
distinguished physical sector.

## Citations (stub)

- Paper 1 (`213/PAPER.md`).
- Lean artifacts: `E213.Research.*`.
- Brouwer, Bishop (constructive math tradition).
