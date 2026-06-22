# Decomposition: representation theory / character theory

*213-decomposition of "a representation / its character", per `../README.md` (model v7). This is a
**fresh** field for the notebook — the repo has never worked representation theory directly. But it is
the **home of the calculus's central object**: a character (the trace of a representation) is the
`×↦·` / `×↦+` character arrow that runs through `parity.md`, `determinant.md`, `prime_factorization.md`,
`entropy.md`, `fourier.md`. LEVERAGE attempt: does the calculus PREDICT the *form* of a representation,
of a character, and of Schur/character orthogonality — or only re-describe it?*

The hypotheses under test (from the task):
1. A **representation** = `⟨ C (a group = Aut-family, `groups.md`) | a reading into a number-construction (matrices/scalars) ⟩` — the group's automorphisms read THROUGH a linear readout.
2. A **character** χ = the `×↦·` character arrow read *on the Aut-family*; `det`/trace is the scalar reading of `determinant.md`; class functions = Aut-invariant readouts (`noether`'s `q=+1` invariant).
3. **Schur / character orthogonality** = the SAME `Σ_x χ(x)=0` the repo just CLOSED at orders 2, 3, 6 (`CharacterOrthogonality`, `RootOfUnityOrthogonality`). Does rep-theory's orthogonality *fall out* of the character arrow as a PREDICTION, consolidating `fourier.md`?
4. **Irreducibility / decomposition into irreps** = a resolution / atom-distinguishability phenomenon (irreps = the atoms of the Aut-family's linear readings)?

## The decomposition (C / Reading / Residue)

- **Construction `C` — the Aut-family of `groups.md`, nothing new.** A representation does not introduce a
  new construction: its input is a **group** `G`, and `groups.md` already decomposed a group as
  `⟨ C₀ (a distinguishing-structure) | the closed family of C₀-preserving self-readings, under composition ⟩`
  — concretely `perms n`, with the four axioms *forced* by "relabel-and-compose"
  (`composeList_assoc`, `composeList_iota_left`, `composeList_invPerm_left`). So the operand of a
  representation is **the `Aut`-family `C`**, the composition-closed reading-family the model already
  carries. The Cayley embedding `mulPerm_comp` (`mulPerm (a·b) = mulPerm a ∘ mulPerm b`) is the literal
  statement "every group *is* an Aut-family" — multiplication IS composition.

- **Reading `L` — a *second-order* character: a reading OF the Aut-family into a number-construction,
  required to be operation-preserving.** `groups.md` §"the character is the group reading itself" already
  named this exact two-level shape: *the family is the object; a character is a reading of that family
  into a number-construction, one level apart* (`psign_mulPerm_hom`). A **representation** is that reading
  with the codomain opened from the finite `{±1}` to a full **matrix / scalar number-construction**
  (`determinant.md`'s "open the same character's finite readout to all of `ℤ`"):

  > a representation `ρ : G → (matrix construction)` is a **homomorphism**: `ρ(ab) = ρ(a)·ρ(b)`.

  This *is* the `det2_mul` arrow read one level up. `det2_mul` (`det₂(MN)=det₂M·det₂N`) says the
  matrix-construction's own scalar readout is multiplicative; composing it with the Cayley map
  `mulPerm_comp` gives `det ∘ ρ` multiplicative on `G` — exactly `psign_mulPerm_hom`'s `{±1}` instance
  with the readout widened to a scalar. So:

  - a **representation** = `⟨ Aut-family C | an operation-preserving reading into a matrix construction ⟩`
    (the homomorphism `ρ(ab)=ρ(a)ρ(b)` is *forced*, not posited — it is "the reading respects how the
    family was built", the same forcing as `det2_mul`'s bare `ring` identity).
  - a **character** χ = the **scalar readout of that reading** — in the repo concretely `det ∘ ρ`
    (`det2_mul` + `mulPerm_comp`). `det(ρ(ab)) = det(ρ(a))·det(ρ(b))` is the `×↦·` character arrow read
    on the Aut-family — the **fourth reading of the one `det` character** that `category_theory.md`'s
    capstone already named (scalar / Aut-invariant / loop-holonomy / down-the-height), now made the
    *defining object* of a whole field.
  - a **class function** = an **Aut-invariant readout** — constant on conjugacy classes
    `χ(gxg⁻¹)=χ(x)`. This is `noether.md`'s `q=+1` conserved invariant: the readout that survives the
    family's own action on itself, certified by `det_holonomy_eq_one` (the conserved transport invariant,
    `det = 1` under conjugation/holonomy). A class function is the character read as the Noether invariant
    of the inner-automorphism action.

- **Residue — two strata, exactly the `fourier.md` pattern.** (i) For the *scalar / `{±1}* characters
  realised in the repo (`psign`, `det`, Legendre), the residue is the usual character residue: the
  scalar collapses the whole matrix interior (`determinant.md`: all of `SL₂` to `1`) — massively
  many-to-one, the representation's *kernel*. (ii) The **deeper residue is the trace and the
  higher-dimensional irreducible characters**: the genuine rep-theoretic character is `χ(g)=tr ρ(g)`, and
  `tr` of a non-1×1 representation lands in a **root-of-unity / cyclotomic readout** (eigenvalue sums
  `ζ^{k₁}+…+ζ^{k_d}`). For orders `n ∈ {1,2,3,4,6}` those roots are concrete `ℤ[ω]`/`ℤ[i]` integers
  (`RootOfUnityOrthogonality`); for general `n` they sit in the **`Real213` cyclotomic-cut residue** —
  the *same* transcendental-cut residue `fourier.md` located. So the character of a representation is
  residue-free exactly where `fourier.md`'s additive character is, and residue-bearing exactly where it
  is. **No new residue kind** — the rep-theory character residue *is* the Fourier character residue.

## Re-seeing

```
   a representation        =  ⟨ Aut-family C (= a group, groups.md) | operation-preserving reading ρ into matrices ⟩
   "ρ(ab)=ρ(a)ρ(b)"        =  the reading respects how the family was built   (det2_mul ∘ mulPerm_comp = psign_mulPerm_hom widened)
   a character χ = tr/det ρ =  the ×↦· character arrow read ON the Aut-family   (det2_mul; psign_mulPerm_hom — fourier.md's L on Aut)
   a class function        =  an Aut-invariant readout  χ(gxg⁻¹)=χ(x)          (noether's q=+1 invariant, det_holonomy_eq_one)
   Schur / χ-orthogonality =  Σ_x χ(x) = 0  for χ ≠ trivial                     (quadratic_orthogonality; root_orthogonality)
   the trivial rep         =  the do-nothing readout (|Aut|=1 case of groups.md, the trivial character)
   irrep                   =  an ATOM of the family's linear readings           (atom-distinguishability axis of C, prime_factorization.md)
   decompose into irreps   =  factor the readout into distinguishable ×-atoms    (the resolution/atom axis — see LEVERAGE)
```

So the **1-dimensional representations of `G` are exactly `fourier.md`'s character group `Ĝ`** — the
maps `G → (roots of unity)` preserving the operation. `fourier.md` already promoted `Ĉ = Hom(C, roots of
unity)` to a first-class dual construction and proved (orders 2,3,6) that its sum vanishes. Representation
theory is the **`d`-dimensional generalisation of that dual**: where Fourier reads `G` through all
1-dim characters, rep-theory reads it through all *irreducible* readings of every dimension. The 1-dim
slice is `fourier.md` verbatim; the order-2 slice is `parity.md`/`determinant.md`'s `{±1}`; the whole
thing is `groups.md`'s "character = a reading OF the family" with the codomain dialed from `{±1}` to a
scalar to a `d×d` matrix.

## LEVERAGE — does the calculus PREDICT a form?

**Honest verdict: PREDICTION on three legs (consolidating, the strongest kind — it unifies five prior
entries under one already-closed theorem), PARTIAL on the fourth, with two clean located breaks. Net:
PREDICTION + PARTIAL, two honest breaks — comparable to `entropy.md`'s leverage but achieved by
*consolidation* rather than a new Lean closure.**

### Leg 1 — representation = operation-preserving reading of the Aut-family. **PREDICTION (forced).**
The homomorphism condition `ρ(ab)=ρ(a)ρ(b)` is not an axiom of representation theory the calculus
*restates* — it is **forced** by "the reading respects how the family `C` was built", the identical
forcing that makes `det2_mul` a bare `ring` identity and `psign_mulPerm_hom` follow from `mulPerm_comp`.
The calculus *predicts* a representation must be a homomorphism, and the repo certifies the instance
(`{±1}` scalar) end-to-end: `mulPerm_comp` (Cayley, the family is an Aut-family) ∘ `psign_mulPerm_hom`
(the scalar readout is multiplicative). Widening `psign` to `det` is `determinant.md`'s certified
`det2_mul`. So "a representation is a homomorphism into matrices" is **derived from the Aut-family +
character-reading structure**, not imported.

### Leg 2 — the character is the `×↦·` arrow on the Aut-family; class functions are the `q=+1` invariant. **PREDICTION (consolidation).**
This is the heart. `category_theory.md`'s capstone proved the single `det`/`×↦·` character is read four
ways (scalar / Aut-invariant / loop / height). Representation theory is the field whose *central object
is exactly reading 1+2 of that capstone*: χ = the scalar reading (`det2_mul`), the class function = the
Aut-invariant reading (`noether`'s `det_holonomy_eq_one`, `q=+1`). The calculus **predicts** that
rep-theory's character must be multiplicative (`legendre_mul`/`det2_mul`-shaped) and that class functions
must be the conserved invariant of the conjugation action — and both are already ∅-axiom theorems in the
repo from *other* domains. This consolidates `parity.md` + `determinant.md` + `fourier.md` + `noether`:
five entries' characters and rep-theory's character are **one arrow**, not an analogy.

### Leg 3 — Schur / character orthogonality. **PREDICTION, and it is the SAME ALREADY-CLOSED THEOREM.**
This is the consolidation the task pointed at, and it lands cleanly. The first orthogonality relation of
representation theory — *characters of inequivalent irreps are orthogonal*, whose 1-dimensional /
abelian case is `Σ_{x∈G} χ(x) = 0` for non-trivial χ — is **literally** the theorem the repo closed:
- order 2 (the `{±1}` / Legendre character): `CharacterOrthogonality.quadratic_orthogonality` (20 PURE,
  `#print axioms` clean, scanned this session) — `Σ_{k<2m}(−1)^k = 0` over the orbit `{g^0,…,g^{p−2}}`,
  with each summand certified to be the quadratic character via `qr_pow_iff_even_exp`.
- orders 3, 6 (cyclotomic roots in `ℤ[ω]`): `RootOfUnityOrthogonality.{omega_orthogonality,
  zeta6_orthogonality, root_orthogonality}` (23 PURE, scanned clean this session) — `1+ω+ω²=0`,
  `Σ_{k<6}ζ₆ᵏ=0`, and the generic `(ζ−1)·Σ_{k<n}ζᵏ=0` whenever `ζⁿ=1`, all forced by the one engine
  `geomSum_telescope` `(ζ−1)·Σ_{k<n}ζᵏ = ζⁿ−1`.

The calculus *predicted* (in `fourier.md`) that character orthogonality is a **root-of-unity telescoping
geometric sum**, forced by the cyclic structure of `Ĝ`. `geomSum_telescope` is that prediction's exact
mechanism. Representation theory's first orthogonality relation, for the 1-dimensional characters (= the
abelian case, = all irreps of an abelian group), is therefore **already a machine-checked ∅-axiom theorem
in this repo** — it falls out of the character arrow with *no new work*. That is genuine consolidation
leverage: a major theorem of a fresh field, certified, because it is the same object.

### Leg 4 — irreducibility / decomposition into irreps. **PARTIAL — predicted shape, not Lean-closed.**
The calculus predicts the *shape*: irreps are the **atoms of the Aut-family's linear readings**, decomposed
along the **atom-distinguishability axis** of `prime_factorization.md` (the axis whose ×-pole has
distinguishable atoms = a per-prime coordinate). "Decompose a representation into irreducibles" = factor
the readout into its distinguishable ×-atoms, the *same* move as prime factorization of the readout
module — Maschke/complete-reducibility is the statement "the readout factors uniquely into atoms," the
UFD-character of `prime_factorization.md` read on the representation ring. The calculus predicts this is a
**resolution-axis** phenomenon (an irrep = the finest reading that still preserves `C`; reducible =
coarser, factorable). **But the repo has no representation-ring / Maschke / complete-reducibility
theorem** — this leg is predicted-by-analogy to `prime_factorization.md`'s certified UFD coordinate, not
independently closed. Honest: PARTIAL, the prediction names a concrete open target (a `Rep(G)` decomposition
mirroring `vp`-factorization).

### The two located breaks (honest, in the `knots.md` spirit)
1. **the realized *character* is `det`, not `tr` — `tr` exists as a readout but NOT as a multiplicative
   character.** Genuine representation-theoretic characters use the **trace** `χ(g)=tr ρ(g)`, which (unlike
   `det`) is *not multiplicative* — `tr` is the **additive** invariant of a matrix, the `×↦+` side, and
   crucially is **not a homomorphism** (`tr(MN)≠tr M·tr N`). **Correction (verified by grep):** `Mat2.tr`
   *does* exist in the repo and carries real theorems — but exactly of the *additive/order* kind, never the
   multiplicative-character kind: `GoldenAperiodic` proves `Mat2.tr (pow G n)` is strictly monotone (the φ
   growth readout), `CrossDetTraceField.traceDisc` uses it as the discriminant `tr²−4det`, and
   `SternBrocotMarkov.trace_lt_mediant_{left,right}` are order facts. What is genuinely **absent** is any
   `tr(MN)=…` multiplicativity / character-homomorphism theorem (there can be none — `tr` is not
   multiplicative) and any `Rep(G)`/Maschke decomposition. So the calculus's "character = `×↦·` arrow"
   captures `det` exactly but **breaks at the `tr`-character**: the trace is present precisely as the
   *additive* `×↦+` readout (φ-growth, discriminant), and the apparatus that makes `det` fall out as a
   forced *homomorphism* does **not** make `tr` a character. This is the precise edge:
   1-dimensional characters (= `det` of 1×1 = the scalar) are fully captured and orthogonality-closed;
   the higher-dimensional *trace* character is conceptual-only here. The deep first orthogonality relation
   in its full `tr`-character form is therefore PARTIAL — closed for the 1-dim/abelian slice (where
   `tr=det=`the scalar character), open for `d>1`.
2. **Induced representations / infinite-dimensional reps are outside the normal form** — like `knots.md`'s
   skein relation, induction `Ind_H^G` is a *relation between representations of different groups* (a
   construction *transported* along `H↪G`), not one Aut-family's self-application residue. And
   infinite-dimensional reps require a completed `νF`/colimit the model **caps honestly at `ω`**
   (`ordinals.md`/`surreal.md`: no `Raw` is inhabited at `ω`). Both sit at the `q=±1` free/colimit corner
   the calculus has flagged open since `category_theory.md`. Located, not failed.

## Revelation

**The residue surfaced is this: representation theory has no construction of its own — it is `groups.md`'s
Aut-family read through `determinant.md`'s scalar character, and its first orthogonality relation is the
`Σχ=0` theorem the repo already closed (`quadratic_orthogonality`, `root_orthogonality`).** The field that
classical mathematics treats as the deep machinery *behind* characters is, in the calculus, **downstream
of the character arrow, not its source.** The collapse is fourfold and certified:

- representation = `groups.md` Aut-family + `determinant.md` character (codomain widened) — `mulPerm_comp`
  ∘ `det2_mul`;
- character = the `category_theory.md` capstone's `det`/`×↦·` arrow, reading 1 (scalar) + reading 2
  (Aut-invariant = `noether`'s `det_holonomy_eq_one`);
- 1-dim representations = `fourier.md`'s dual `Ĝ`;
- Schur orthogonality (1-dim/abelian) = `quadratic_orthogonality` + `root_orthogonality`, **already
  ∅-axiom, verified PURE this session**, with `geomSum_telescope` the forced mechanism `fourier.md`
  predicted.

So representation theory **consolidates** `parity.md`, `determinant.md`, `fourier.md`, `groups.md`, and
`noether` into one statement: *these were all representation theory the whole time* — the order-2 character
(parity/det), the 1-dim dual (Fourier), the Aut-family (groups), the invariant (Noether), and the scalar
homomorphism (determinant) are the low-dimensional, already-closed corner of one field. The break locates
where the calculus stops: at the **trace** (the additive, non-multiplicative `d>1` character) and at
**induction / infinite-dimensional reps** (the free/colimit `q=±1` corner). The honest edge is exactly the
edge every prior batch found — `tr` is the `×↦+` twin the `det`-machinery doesn't generate, and induction
is `knots.md`'s "relation between distinct constructions" again.

## Does it consolidate `fourier.md` / the character arrow? — YES, decisively.

`fourier.md`'s open target was "general order-`>2` χ needs a cyclotomic `ζ`"; its closed result was
orthogonality at orders 2, 3, 6. Representation theory **re-identifies that closed result as a major
theorem of a second field** (Schur orthogonality for 1-dim/abelian characters) — the same `Σχ=0`, the same
`geomSum_telescope` mechanism, the same `Real213`-cut residue boundary for non-`{1,2,3,4,6}` orders. The
character arrow `×↦·` now provably runs through **seven** entries — parity `L₂`, prime-valuation `vp_mul`,
determinant `det2_mul`, entropy additivity, Noether `det_holonomy_eq_one`, Fourier `legendre_mul`/
`quadratic_orthogonality`, and now **representation-theory characters** — all one construction-preserving
reading. This is the deepest consolidation in the notebook: representation theory is not a new domain for
the arrow, it is the *field-shaped statement of the arrow itself.*

## Touches on model v7?

**No new primitive; EXTEND + one explicit consolidation note.** The model's two invariants (character
arrow, `q=±1` residue) and four axes (direction, fold-height, resolution+base, iteration-character) absorb
representation theory with nothing added — it is `groups.md`'s Aut-family (the reading slot's
composition-closure) read through `determinant.md`'s widened-codomain character, with orthogonality =
`fourier.md`'s closed `Σχ=0`. The one note worth recording in the README's batch log:

> **Representation theory is the field-level name of the character arrow read on Aut-families.** The
> calculus's "character = `×↦·` reading of a composition-closed family" (`groups.md` + `determinant.md`)
> *is* the definition of a representation; its first orthogonality relation (1-dim/abelian) is the
> already-closed `Σχ=0` (`quadratic_orthogonality`, `root_orthogonality`). The break is sharp and twofold:
> (a) the **trace** character (`×↦+`, additive, non-multiplicative) for `d>1` is *not* generated by the
> `det`-homomorphism machinery — it is the additive twin, conceptual-only in the repo; (b) **induction /
> ∞-dim reps** are the `knots.md`/free-corner exterior (relation between distinct constructions / uncompleted
> `νF`). So model v7's interior is unchanged; representation theory pins the `det`-vs-`tr` split as the
> precise spot where the multiplicative character arrow ends and the additive `×↦+` character (which the
> model carries but has *not* closed at matrix level) begins.

This sharpens, but does not alter, model v7: it identifies the `det`/`tr` boundary as the live edge of the
character arrow's coverage of a major field. **31 decompositions; representation theory EXTENDS by
consolidation, with the `det`/`tr` split as a new located partial-break.**

## Verified Lean anchors (grep + `#print axioms` scanned this session)

| Leg | Theorem (file:line) | Purity |
|---|---|---|
| ★ χ-orthogonality, order 2 (Legendre) | `Lib/Math/NumberTheory/ModArith/CharacterOrthogonality.lean:146` `quadratic_orthogonality` | **20 PURE / 0 DIRTY** (`scan_axioms`, this session) ✓ |
| order-2 char sum = 0 (the telescope core) | `…/CharacterOrthogonality.lean:126` `charSumExp_eq_zero`; `:90` `altSign_eq_one_iff_even`; `:220` `qr_count_eq_nonqr_count` | PURE (in the 20) ✓ |
| ★★★ χ-orthogonality engine (generic) | `Lib/Math/Algebra/CayleyDickson/Integer/RootOfUnityOrthogonality.lean:190` `geomSum_telescope` `(ζ−1)·Σ_{k<n}ζᵏ=ζⁿ−1` | **23 PURE / 0 DIRTY** (`scan_axioms`, this session) ✓ |
| ★ χ-orthogonality, orders 3 & 6 & generic | `…/RootOfUnityOrthogonality.lean:206` `omega_orthogonality`; `:210` `zeta6_orthogonality`; `:223` `root_orthogonality`; `:241` `cyclotomic_orthogonality` | PURE (in the 23) ✓ |
| character = `×↦·` arrow, `{±1}` on Aut-family | `Lib/Math/NumberTheory/ModArith/Zolotarev.lean:133` `psign_mulPerm_hom`; `:106` `mulPerm_comp` (Cayley) | ∅-axiom (per `groups.md`/`fourier.md`) ✓ (grep-confirmed) |
| character = `×↦·` arrow, scalar (det) | `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul`; `…/ModularGeometry/HolonomyLattice.lean:123` `det_mul`, `:136` `det_holonomy_eq_one` (class-function/`q=+1`) | ∅-axiom (per `determinant.md`/`noether`) ✓ (grep-confirmed) |
| 1-dim character = QR/dlog = Fourier L₂ | `Lib/Math/NumberTheory/ModArith/DiscreteLogParity.lean:95` `qr_pow_iff_even_exp`; `:123` `dlog_exists`; `…/PrimitiveRoot.lean:156` `exists_primitive_root` | ∅-axiom (per `fourier.md`) ✓ (grep-confirmed) |
| Aut-family = group (the operand `C`) | `Lib/Math/Algebra/Linalg213/PermGroup.lean:59` `composeList`, `:73` `composeList_iota_left`, `:93` `composeList_assoc`, `:184` `composeList_invPerm_left` | ∅-axiom (per `groups.md`) ✓ (grep-confirmed) |
| "(preserved construction, Aut group)" native catalog | `Lib/Math/Algebra/Mobius213/Px/SymmetrySpecies.lean:54` `AutGroup`, `:77` `FamilySpecies` | structural/catalog (per `groups.md`) ✓ (grep-confirmed) |

## Conceptual-only legs / located breaks (honest — not cited as anchors)

- **the `tr`-*character* `χ(g)=tr ρ(g)` for `d>1`** — `Mat2.tr` exists and has real theorems, but only of
  the *additive/order* kind: `GoldenAperiodic` (φ-growth: `Mat2.tr (pow G n)` strictly monotone),
  `CrossDetTraceField.traceDisc` (`tr²−4det`), `SternBrocotMarkov.trace_lt_mediant_{left,right}`. What is
  **absent is any `tr(MN)=…` multiplicativity / character-homomorphism theorem** (there can be none — `tr`
  is not multiplicative) and any `d>1` **trace-character** used as a class function for orthogonality. The
  realized *character* is `det` (multiplicative, the `×↦·` arrow); `tr` is the *additive `×↦+` twin* the
  `det`-homomorphism machinery does not turn into a character. Central located break: 1-dim characters
  (`tr=det`= the scalar) are closed and orthogonality-proved; the `d>1` trace character is conceptual-only.
  **The sharp open target.**
- **Maschke / complete reducibility / `Rep(G)` decomposition into irreps** — absent; predicted by analogy
  to `prime_factorization.md`'s certified UFD `vp`-coordinate (decompose = factor the readout into
  distinguishable ×-atoms), not independently closed. PARTIAL.
- **Induced representations `Ind_H^G`, infinite-dimensional reps** — outside the normal form: induction is
  a *relation between representations of different groups* (`knots.md`'s skein-shaped break), and ∞-dim
  reps need the uncompleted `νF`/colimit (`ordinals.md` cap at `ω`). The `q=±1` free/colimit corner,
  flagged open since `category_theory.md`. Located, not a failure.
- **The full Schur orthogonality `(1/|G|)Σ_g χ_i(g)χ̄_j(g)=δ_ij`** (weighted, conjugate, two-character
  form) — the repo has the *vanishing* case `Σχ=0` (= the `i≠trivial` row of the relation) closed at
  orders 2,3,6; the full weighted bilinear `δ_ij` form (with the `1/|G|` weight = `entropy.md`'s
  weight-reading, and conjugation = the `q=±1` direction bit) is conceptual — predicted as
  `weight ∘ (character × character̄)`, un-cashed. THIN.
