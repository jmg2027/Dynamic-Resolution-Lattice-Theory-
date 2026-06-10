# Multiplicity doctrine (framework-internal coexistence)

**Status**: Doctrine chapter; consolidates Pattern #17 + Pattern #20
of `theory/meta/methodology_patterns.md` and the four canonical
instances they document.  No new Lean — the chapter names a
discipline already practiced across the corpus.

## The doctrine

When a categorical concept admits multiple framework-internal
realisations, 213 keeps all of them as parallel Lens outputs and
does not pick a canonical one.  Multiplicity is not indecision; it
is the operational reading of "Lens application IS distinguishing,
not a tool above Raw" — each realisation is one distinguishing
choice on the same Raw structure, and choosing one would import a
preferred frame that the axiom set explicitly refuses.

This generalises framework-internal subsumption (Pattern #17 —
classical constructions absorbed into 213's Lens space) to
**multiplicity within 213** itself: 213 not only subsumes external
canonical forms, it also refuses an internal canonical form once
more than one exists.

## Four canonical instances

### Instance 1 — Real number carriers

Three coexisting realisations of "a real number":

| Realisation | File | Form |
|---|---|---|
| `Real213` struct | `Math/Real213/Core/Core.lean` | Dedekind-cut + modulus |
| `RealAsLensOutput` | `Math/Real213/Core/AsLensOutput.lean` | `Nat → Nat → Bool` |
| `DyadicBracket` | `Math/Analysis/DyadicSearch/DyadicBracket.lean` | finite-precision bracket |

`RealAsLensOutput` is the bare `Nat → Nat → Bool` cut-function
abbreviation; `Real213` packages the cut with an explicit modulus
witness; `DyadicBracket` carries an analysis-time finite interval
sufficient for ε-replacement bookkeeping.  Each is the canonical
choice for *one* purpose (Lens-output reasoning, structural
algebra, numerical analysis) and none is the canonical choice
overall.  Chapter: `theory/math/numbersystems/real213.md`.

### Instance 2 — Derivative forms

Three coexisting realisations of "the derivative":

| Realisation | File | Form |
|---|---|---|
| classical limit | (referenced, not formalised) | ε-N existential |
| `localDivergence` | `Math/Analysis/FluxMVT/FluxDivergence/FluxCut.lean` | `(Raw → Real213) → Nat → Real213` via `flux × 2^expE` |
| `IsDifferentiable` | `Math/Analysis/Differentiation/Differentiation.lean` | explicit derivative-data record with modulus |

The classical limit form is named only as the classical baseline
that 213 does not adopt.  `localDivergence` is the 213-native
flux-cut form, and `IsDifferentiable` packages the explicit
derivative-data form used in `ClassicCalc`.  Bridge: `ClassicCalc`
binds the two formalised forms.  Chapter:
`theory/math/analysis/differentiation.md`.

### Instance 3 — Cup products

Two coexisting realisations of "the cup product":

| Realisation | File | Form |
|---|---|---|
| `cup` (lex-projection) | `Math/Cohomology/Cup/Core.lean` | single sorted partition `(α ⌣ β)(τ) = α(τ.take k) · β(τ.drop k)` |
| `cupAW` (Alexander-Whitney) | `Math/Cohomology/CupAW/` (21+ files) | homotopy-coherent variant satisfying graded Leibniz per bidegree |

Both are `Cochain n k`-valued; both are ∀(n, k, l) PURE.  The
lex-projection cup admits a modified Leibniz with a single
un-cancelled middle-face term (`δ(α⌣β) = δα⌣β ⊕ α⌣δβ ⊕
α⌣β | τ\{τ[k]}`); the AW cup satisfies the standard graded
Leibniz.  Neither is canonical — `cup` carries the self-referential
Leibniz closure, and `cupAW` carries the per-bidegree
grading that closes the K_{3,2}^{(c=2)} cohomology stack.
Chapter: `theory/math/cohomology/cup.md` (and `cupaw.md`).

### Instance 4 — Modulus structures

Three coexisting realisations of "a modulus" (target-precision ↦
step-count):

| Realisation | File | Property |
|---|---|---|
| `IsContinuousModulus` | `Math/Topology/Continuity.lean` | monotone (`∀ k, modulus k ≥ k`) |
| `IsRicciModulus` | `Math/GeometrizationConjecture/Ricci.lean` | anti-monotone |
| `dyadic_bracket_cauchy_modulus` | `Math/Analysis/.../DyadicBracket.lean` | linear `L · k` |

All three are `Nat → Nat` annotated with a positional-control
property.  The directional convention (monotone / anti-monotone)
is the only differentiator; the underlying data type is identical.
The 3-way bridge is recorded in
`lean/E213/Lib/Math/Geometry/Topology/ModulusStructure.lean` via
`IsModulusStructure` projections.  Chapter:
`theory/math/analysis/modulus_structure.md`.

## Why multiplicity

The doctrine is not stylistic; it is the operational reading of
the no-exterior axiom (`seed/AXIOM/05_no_exterior.md` §5.1).  Each
realisation is a distinguishing — one Lens output of the same Raw
substrate.  Picking one realisation as canonical would amount to
declaring one Lens preferable to the others, which is the
"comparison frame" failure mode catalogued in `CLAUDE.md`.

The framework records all framework-internal realisations as
first-class objects and treats the bridges between them as the
content.  This is how the Bishop programme is absorbed (Pattern
#17): not by picking a 213-canonical real and showing classical
reals reduce to it, but by exhibiting the Lens-output space that
*already contains* every Bishop construction as one of its
inhabitants.

## Bridges (where they exist)

Multiplicity does not mean disconnection.  Where pairs of
realisations both apply, 213 records explicit bridges:

- Real213 ↔ RealAsLensOutput: `Real213_to_LensOutput` and inverse.
- `IsDifferentiable` ↔ `localDivergence`: `ClassicCalc` binding.
- `cup` ↔ `cupAW`: lex-projection vs AW relation at low bidegrees
  (proven coincident for the cases that overlap; divergent at
  bidegree where the lex-cup's single-face correction matters).
- The three modulus realisations all project to one bare
  `IsModulusStructure`; the 3-way bridge is the
  `ModulusStructure.lean` typeclass.

Bridges are the content of the doctrine.  The multiplicity is
visible *only because* the bridges make it observable; otherwise
the realisations would be three disconnected sub-trees with the
same name.

## Open frontier

- **4-way modulus extension**: the α_em `zeta_modulus` in
  `theory/physics/alpha_em/precision_derivation.md` Step 6 is a
  fourth modulus realisation (Gram-correction step-count).  It is
  not yet folded into the `IsModulusStructure` bridge.
- **More categorical concepts**: integrals, limits, neighbourhood
  systems — any new concept with multiple in-corpus realisations
  is a candidate for explicit multiplicity registration.

## Cross-references

- `theory/meta/methodology_patterns.md` Pattern #17 — framework
  subsumption of external (Bishop, classical) constructions
- `theory/meta/methodology_patterns.md` Pattern #20 — multiplicity
  within the framework (instances above)
- `theory/math/numbersystems/real213.md` — Instance 1
- `theory/math/analysis/differentiation.md` — Instance 2
- `theory/math/cohomology/cup.md`, `cupaw.md` — Instance 3
- `theory/math/analysis/modulus_structure.md` — Instance 4
- `seed/AXIOM/05_no_exterior.md` §5.1 — no-exterior axiom (the
  doctrine's source)
