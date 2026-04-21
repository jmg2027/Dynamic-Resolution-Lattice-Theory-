# The ℝ-algebra Assumption in 213: A Finitist Critique

**Mingu Jeong**

*Independent Researcher*

---

## Abstract

The companion paper *The Minimal System of Binary Relations*
(PAPER, hereafter "Paper 1") derives from a three-clause axiom
a single self-recognising Lens codomain, the field of complex
numbers `ℂ`, via five structural constraints R1–R5 that any
Lens internal to the axiom's space `Raw` must respect. This
paper dissects R5 and shows that its "minimality /
completeness" half imports classical set-theoretic infinity
that the three-clause axiom itself does not supply. Once that
half is removed, the R1–R4 fragment admits a **countable
infinity** of admissible Lens codomains, Lean-verified here
for the parametric family `ℤ[√-D] (D > 0)` plus the
Eisenstein integers `ℤ[ω]`. We conclude that Paper 1's "ℂ
uniqueness" holds only under a classical-infinity assumption
that is not internal to the axiom, and propose a purely
finitist reformulation of R5 under which ℂ is not forced but
is one admissible Lens among many.

All counterexamples are Lean 4 core only (no Mathlib), 0
`sorry`, 0 axioms beyond Paper 1's three clauses.

---

## 1. Recap of Paper 1

Paper 1's three-clause axiom produces a single type `Raw` —
the free commutative magma on two generators with no fixed
points — and nothing else. Observation requires a *Lens*
`L = (α, base_a, base_b, combine)` that folds Raw into a
codomain `α`.

For a Raw-internal object to recognise itself Paper 1
identifies five structural constraints R1–R5 on L:

- **R1, R2** — binary combine + catamorphism (homomorphism
  from free commutative magma to `(α, combine)`).
- **R3** — non-vanishing: `combine` has no zero divisors.
- **R4** — swap matches exactly one nontrivial `ℝ`-algebra
  automorphism `conj : α → α` with `conj² = id`, `conj ≠ id`.
- **R5** — reception of infinite structural branches: every
  non-terminating Raw trajectory has a unique state in `α`.

Paper 1 §4 proves that R1–R5 force `α ≅ ℂ` up to `ℝ`-algebra
isomorphism, with `Raw.swap` corresponding to complex
conjugation.

The derivation's algebraic step (§4.1 F1–F4) assumes "α is an
`ℝ`-algebra" and classifies finite `ℝ`-field extensions.
The present paper asks: **where does the `ℝ`-algebra premise
come from?** The answer — R5 — motivates the critique.

---

## 2. The two halves of R5

Paper 1 states R5 as a single condition on the codomain, but
it conflates two logically distinct claims.

### 2.1 R5a — Distinguishing

Every `r : Raw` has a unique image under `L.view`, i.e.
`L.view` is injective. In Lean this is the
`E213.Meta.LensCatalog.Distinguishing` predicate.

R5a is **non-trivial**: swap-blind Lenses (e.g.
`Lens.leaves`, `Lens.depth`, where `base_a = base_b`) fail
it because they collapse the `a ↔ b` distinction to a single
natural-number image. R5a therefore does real work,
selecting injective / swap-visible Lenses.

### 2.2 R5b — Completeness / infinite-branch reception

Every *non-terminating structural branch* of Raw — an
infinite sequence of `slash` applications — has a **unique
determined state** in `α` under the observation rule. Paper
1 §3.2 acknowledges:

> Such branches do not themselves produce R-terms (every
> R-term is finite).

That is: non-terminating branches are **not** elements of
the inductive type `Raw`. To quantify over them one must
sit in a coinductive / classical ambient. Neither is
supplied by the three-clause axiom.

Within `inductive Raw` (the Lean 4 encoding of the axiom),
R5b's universal reduces to `∀ _ ∈ ∅, P` — vacuously true.
This is formalised as:

```lean
theorem E213.Research.R5Vacuity.foldTotality_vacuous :
    ∀ L : Lens α, ∀ r : Raw, ∃ a : α, L.view r = a :=
  fun L r => ⟨L.view r, rfl⟩
```

In other words, R5b **cannot be stated non-trivially** over
the axiom's type. Stating it requires importing a coinductive
/ classical ambient.

### 2.3 Where R5b enters Paper 1 §4

Paper 1 §4 intro declares:

> R1, R2, R3, R5 together force the base `ℝ`. R4 extends
> `ℝ` to `ℂ`.

The "force the base `ℝ`" step uses R5b's completeness to
argue:
1. Every non-terminating branch maps to a unique codomain
   element.
2. The codomain is Cauchy-complete with respect to a
   natural convergence notion on branches.
3. Combined with R1–R3 (no zero divisors, binary combine,
   catamorphism), the minimal such codomain is `ℝ`.

Without R5b, step (1) is vacuous (no such branches in
inductive Raw), step (2) is unjustified, and the minimal
codomain conclusion fails. The `ℝ`-algebra premise in §4.1
is therefore supported only by R5b — the classical-infinity
part.

R5a alone does **not** imply the codomain contains `ℝ`. A
countable field like `ℚ[i]` can be injectively reached by
a Lens (R5a holds) without containing `ℝ`.

---

## 3. Explicit counterexamples under R1–R4 alone

If R5b is the sole source of the `ℝ`-algebra premise, then
removing it should admit codomains that are not
`ℝ`-algebras.  We exhibit four families.

### 3.1 Three concrete witnesses

Each is a `structure … where re : Int; im : Int`, with
custom `mul`, `conj`, `normSq`, satisfying R1–R4 via a
`R4Codomain` instance in `E213.Meta.SelfRecognising`.

| Codomain | Norm | Instance |
|---|---|---|
| `ZI = ℤ[i]` (Gaussian) | `a² + b²` | `E213.Research.ZIInstance` |
| `Z2 = ℤ[√-2]` | `a² + 2b²` | `E213.Research.Z2Instance` |
| `ZOmega = ℤ[ω]` (Eisenstein) | `a² − ab + b²` | `E213.Research.ZOmegaInstance` |

All three are countable — directly contradicting Paper 1
§4's cardinality-`𝔠` conclusion from R5.

### 3.2 A parametric family

`E213.Research.ZSqrt D = ℤ[√-D]` for `D : Int`:

```lean
structure ZSqrt (D : Int) where
  re : Int
  im : Int

def ZSqrt.mul (u v : ZSqrt D) : ZSqrt D :=
  ⟨u.re * v.re - D * (u.im * v.im),
   u.re * v.im + u.im * v.re⟩

def ZSqrt.normSq (u : ZSqrt D) : Int :=
  u.re * u.re + D * (u.im * u.im)
```

The generic theorem
`ZSqrt.R4_of_pos : 0 < D → R4Codomain (ZSqrt D)` produces
an instance for any positive `D`.  Concrete instances
`D = 3, 5, 7` are one-liners; adding `D = 11, 13, 17, …`
is likewise.

This family is a **countable infinity** of R1–R4-admissible
codomains, parametrised by `D`.  None contains `ℝ`.

### 3.3 Lean infrastructure

The counterexamples exploit custom metaprogramming built
on top of Lean 4 core (no Mathlib):

- `E213.Tactic.QuadNorm` — macro closing Diophantus-style
  norm-multiplicativity identities via
  `simp` (11-lemma arithmetic AC set) + `omega`.
- `E213.Tactic.DeriveR4Codomain` — `command_elab` that
  synthesises the 13-field `R4Codomain` instance from a
  naming-convention spec.
- `E213.Research.IntHelpers` — shared `a·a` lemmas.
- `E213.Meta.SelfRecognising` — 4-tier typeclass chain
  `R12Codomain → R3Codomain → R4Codomain`.

Each new instance is two ingredients: a domain file (~50–95
lines of arithmetic proofs, mostly `quad_norm`) and a
one-line `derive_r4_codomain` or `ZSqrt.R4_of_pos` call.

### 3.4 What the counterexamples show

Paper 1's ℂ-uniqueness conclusion is **false** under the
R1–R4 fragment.  The full R1–R5 conclusion survives only
because R5b imposes a cardinality / completeness condition
that rules out countable codomains.  But R5b is not
expressible within the axiom's inductive type, so the
conclusion depends on imported classical machinery.

---

## 4. Implications

### 4.1 Status of Paper 1's main theorem

Paper 1 Theorem 4.1 (Self-recognising Lens is ℂ) remains
**valid as stated** — but its hypotheses include R5b, which
in turn requires a classical ambient beyond the axiom.
Paper 1's "no stipulations" table (Conclusion) lists R5 as
grounded in "Raw's non-terminating generation rule (no
crash)"; the present analysis refines this: the no-crash
half (R5a) is finitary and genuine, while the completeness
half (R5b) is the smuggling channel.

### 4.2 Status of ℂ in 213

Without R5b, ℂ is **one admissible codomain among many**
rather than the unique self-recognising Lens. The
counterexamples show the spectrum includes at least:
- all quadratic imaginary rings `ℤ[√-D]` for `D > 0`
- Eisenstein integers `ℤ[ω]`
- and presumably more (extensions to `ℚ[√-D]`, higher-degree
  algebraic number rings, etc., are straightforward).

ℂ's special status, if any, must come from a condition
external to R1–R4: physical relevance (quantum mechanics,
interference, unitarity), categorical universal property
(initial / terminal object in some category of lenses), or
a further 213-internal constraint yet to be discovered.

### 4.3 Finitist reading

Under a strict finitist reading of the axiom — where
inductive Raw is the only substrate and coinductive /
classical completions are off-limits — R5 reduces to R5a.
The 213 framework then provides:

- A **pre-mathematical** substrate (`Raw`).
- A **free choice** of measurement Lens, each producing a
  distinct extracted mathematics.
- ℂ as one **distinguished** Lens with physical significance,
  not an internal mathematical necessity.

This reading aligns with the constructive / intuitionist
tradition (Brouwer, Bishop) and is consistent with the
213 research programme's broader claim that "mathematics
emerges from 213 via Lens choices."

---

## 5. Finitist reformulation: R5 → R5a

We propose the following finitist replacement for Paper 1's
R5, preserving Paper 1's genuine content while discarding
the classical-infinity smuggling.

### 5.1 R5a as the sole R5 condition

**(R5a — Distinguishing.)** `L.view : Raw → α` is injective:

```lean
def Distinguishing {α : Type} (L : Lens α) : Prop :=
  Function.Injective L.view
```

Under this reading, R5 says only that different Raw terms
must have different measurements — a purely finitary
condition, well-defined on the inductive type, already
formalised in `E213.Meta.LensCatalog`.

### 5.2 What R1–R4 + R5a determines

With R1–R4 + R5a, the class of admissible codomains is:
- any commutative ring with a `ℤ/2`-group automorphism
  matching `Raw.swap`,
- having no zero divisors,
- in which `L.view` is injective.

This class is **large**: it includes all countable rings
exhibited in §3, plus (by straightforward extension):
- rational cousins `ℚ[√-D]`,
- higher-degree algebraic number rings admitting a
  nontrivial `ℤ/2` automorphism,
- finite fields `𝔽_{p²}` for odd `p` (characteristic
  requires care but the predicate structure survives).

### 5.3 ℂ as a distinguished, not unique, Lens

`ℂ` is admissible (it satisfies R1–R4 + R5a). Its privileged
status, if any, must arise from outside the axiom:

- **Physical**: quantum mechanics, interference, unitary
  evolution — empirical evidence that ℂ is the Lens used by
  Nature.
- **Categorical**: ℂ may be initial / terminal / limit in
  some natural category of R1–R4-admissible codomains; this
  is an open question (see `notes/03_e4_restoring_c.md`).
- **Archimedean / ordered closure**: ℝ's real-closed status
  and ℂ's algebraic closure over ℝ characterise the pair
  uniquely among ordered fields — but "ordered" and
  "complete" are external to the axiom.

Paper 1's main theorem should therefore be read as:
"under R1–R5 (R5 including R5b), ℂ is forced," with the
understanding that R5b is an **external classical
assumption**, not a 213-internal structural constraint.

### 5.4 Relation to constructive mathematics

R5a is a constructively acceptable condition (injectivity
on a decidable equality type). R5b demands ambient
classical reasoning (either coinductive types or
set-theoretic completion). The finitist reading of 213 thus
places it in the Brouwer–Bishop tradition, where
completions are processes rather than completed objects.

This is not an endorsement of strict finitism for all of
mathematics — merely the observation that **the 213 axiom
itself** does not supply classical infinity, and any
conclusion depending on classical infinity must name the
import.

---

## 6. Conclusion

Paper 1 presents the 213 framework as a derivation from a
single three-clause axiom to the complex numbers `ℂ`. We
have argued that the final step — "`ℂ` is the unique
self-recognising codomain" — rests on the R5b half of R5,
which is a classical-infinity condition not supplied by
the axiom.

With R5b removed, the R1–R4 + R5a fragment is satisfied by
a countable infinity of codomains, Lean-verified here:
`ℤ[i]`, `ℤ[√-2]`, `ℤ[ω]`, and the parametric family
`ℤ[√-D]` for `D > 0`. The ℂ-uniqueness claim therefore
holds **only modulo a classical-infinity assumption**.

Three readings remain open:

1. **Retain R5b as an external classical import.** Paper 1
   is correct; the ℂ-uniqueness theorem requires ZFC-style
   completion reasoning; this is explicit and acknowledged.

2. **Replace R5 with R5a (finitist reading).** 213 is a
   pre-mathematical framework; mathematics emerges from
   Lens choices; ℂ is one admissible Lens among many; its
   physical distinction is an empirical fact, not a
   mathematical necessity.

3. **Find a Raw-internal replacement for R5b.** If there
   exists a 213-internal condition (categorical, structural,
   physical) that uniquely selects ℂ without classical
   infinity, this restores the uniqueness claim while
   keeping the framework finitary. This is an open
   research question.

The authors lean toward reading (2) for the 213 research
programme, with reading (3) as the active research target.
Reading (1) stands as a valid interpretation if the reader
accepts classical infinity as a background assumption.

In any reading, **Paper 1's Lean-verified content (R1–R4
forcing a specific algebraic structure, modulo the base
`ℝ`-algebra premise) stands**. The contribution of the
present paper is to locate and name the premise.

---

## Acknowledgments

This work was developed in dialogue with Claude (Anthropic).
All mathematical content was verified by the author. The
Lean 4 formalisation of the counterexamples
(`E213.Research.{ZI,Z2,ZOmega,ZSqrt}*` modules + the
`E213.Tactic.{QuadNorm,DeriveR4Codomain,IntSquare}` custom
tactics) is by the author, pure Lean 4 core (no Mathlib),
0 `sorry`, 0 axioms beyond Paper 1's three clauses.

## Code availability

The Lean 4 framework and all counterexample modules are in
`213/framework/` in the source repository. Build:
```
cd framework && lake build
```
No external dependencies beyond Lean 4 core (v4.16.0).

## Cross-references

- Paper 1: `213/PAPER.md`
- Research notes: `213/research/r5-critique/notes/*`
- Lean artifacts: `213/framework/E213/Research/*`,
  `213/framework/E213/Tactic/*`,
  `213/framework/E213/Meta/SelfRecognising.lean`
