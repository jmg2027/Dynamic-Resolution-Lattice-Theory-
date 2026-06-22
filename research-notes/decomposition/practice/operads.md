# Decomposition: operads / higher algebra (composition ∘ᵢ, the axioms, A∞/E∞, the operads Assoc/Comm/Lie)

*213-decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants + the
2-category of readings + the fold/composition `Raw.fold`/`raw_initial`). A **fresh** field, chosen to
test one thesis: **an operad is the calculus's own composition/fold structure made arity-graded** —
the `Raw.slash` distinguishing iterated by `Raw.fold`, but indexed by arity `n` (operations of `n`
inputs composed via `∘ᵢ`). The associativity/equivariance/unit axioms = the fold's coherence (the
`raw_initial` uniqueness / `dhom_unique_pointwise` that makes composition well-defined); the specific
operads (Assoc/Comm/Lie) = the fold / symmetric-`slash_comm` / antisymmetric readings; A∞ coherence =
the associahedron = Catalan; algebras over an operad = the Lens-images carrying the operations. NO new
primitive — it is `two_cells.md`'s 2-category of readings made arity-explicit. The bar is
PREDICTION/REVELATION (not collapse-only: this consolidates `category_theory.md` + `two_cells.md` +
`lie_theory.md` + `curry_howard.md`).*

## The decomposition (C / Reading / Residue)

- **Construction `C` — the distinguishing, made arity-graded.** The calculus's generative act is the
  *binary* distinguishing `Raw.slash : (x y : Raw) → x ≠ y → Raw` (`Theory/Raw/Slash.lean`), iterated
  by the catamorphism `Raw.fold base_a base_b combine` (`Theory/Raw/Fold.lean:22`). An operad asks for
  this same act at **every arity `n`**: an `n`-ary operation `θ ∈ 𝒪(n)` takes `n` inputs, and `∘ᵢ`
  substitutes one operation into the `i`-th slot of another. The repo already hosts the arity-graded
  signature: `CombinatorialArity.Raw k` has a `k`-ary relation constructor `rel : (Fin k → Raw k) →
  Raw k` (`Theory/Atomicity/CombinatorialArity.lean:90`) — operations of arity exactly `k`, with the
  `i`-th input the `i`-th coordinate of `Fin k → Raw k`. So `C` = the distinguishing read **as a family
  of `n`-ary operations**, the operad's underlying collection `{𝒪(n)}ₙ`. The binary `Raw.slash` is
  `𝒪(2)`; nesting (`Raw.fold`) is the operadic composition tree.

- **Reading `L_∘` (the operadic-composition reading)** — fold a *tree of operations* into one operation
  by substituting at slots: `(θ ∘ᵢ ψ)` plugs `ψ` into slot `i`. On the calculus this is exactly
  `Raw.fold`: a `Raw` term *is* a composition tree of binary slashes, and `Raw.fold base base combine`
  is the unique map evaluating that tree by composing `combine` at every node. The operad axioms are
  the fold's coherence: **associativity of ∘ᵢ** (substituting then substituting = substituting in one
  step) is `Raw.fold_slash` (`Theory/Raw/Fold.lean:37`, the homomorphism `fold(slash x y) = combine
  (fold x)(fold y)`) propagated by `Raw`-induction; **uniqueness of the composite** (the operad's
  operations are determined, no ambiguity) is `raw_initial` (`SemanticAtom.lean:412`) + the pointwise
  uniqueness `dhom_unique_pointwise` (`UniversalDistinguishing.lean:103`). So `L_∘` = the fold, read on
  trees-of-operations rather than trees-of-points.

- **Residue — `q = ±1`, at the symmetry/coherence pole.** Two residues stack here. (1) **The
  equivariance / symmetric-group action** — `𝒪(n)` carries a `Σₙ`-action permuting inputs; the residue
  is the `q = ±1` direction bit of `two_cells.md`/`integers.md`: the symmetric (Comm) operad quotients
  by `slash_comm` (the directionless `a/b = b/a`, `Theory/Raw/Slash.lean:40`, `q=+1`), the Lie operad
  by the *antisymmetric* sign (`bracket_antisymm`, `q=−1`). (2) **The coherence-up-to-homotopy residue
  (A∞/E∞)** — associativity holding only *up to coherent homotopy* is the resolution dial carried as
  *data*: the witness-carrying pattern of `FreeReduction` (the normal-form Σ-quotient, no `Quot`) and
  the associahedron, whose face-count is **Catalan** (`Catalan.catalan_recursion_n`). The residue is
  the surplus the strict-fold reading leaves: the higher coherences the binary fold forces but does not
  itself name.

## Re-seeing (⟨C | L⟩)

```
   an operad 𝒪            =  ⟨ the distinguishing as a family {𝒪(n)}ₙ of n-ary ops | the fold ∘ ⟩
   the collection 𝒪(n)    =  k-ary distinguishing: rel : (Fin k → Raw k) → Raw k   (CombinatorialArity)
   binary op 𝒪(2)         =  Raw.slash  (the generating distinguishing)
   composition θ∘ᵢψ        =  Raw.fold: substitute ψ into slot i, evaluate the tree   (Raw.fold)
   ∘ᵢ-associativity        =  fold homomorphism: fold(slash x y)=combine(fold x)(fold y)  (Raw.fold_slash)
   unit (id ∈ 𝒪(1))        =  fold on a leaf: fold base_a Raw.a = base_a              (Raw.fold_a)
   composite is unique     =  raw_initial / dhom_unique_pointwise (the only fold out of Raw)
   equivariance (Σₙ-action) =  the q=±1 direction bit on the input-slots
   the associative operad  =  the strict Raw.fold linear composition (no symmetry quotient)
   the commutative operad  =  the slash_comm symmetric quotient (q=+1, a/b = b/a)
   the Lie operad          =  the antisymmetric bracket [X,Y]=XY−YX, q=−1 (lie_theory.md, Mat2Bracket)
   an algebra over 𝒪       =  a Lens-image: an object carrying 𝒪's operations (view : Raw → α)
   A∞ (assoc up to homotopy) =  the resolution dial carried as DATA; coherence witnesses (FreeReduction)
   the associahedron Kₙ     =  the coherence polytope, #faces counted by Catalan (catalan_recursion_n)
   E∞ (commutative up to ∞-coherent homotopy) =  slash_comm at every coherence height (the q=+1 corner)
   May recognition (E∞ ⟺ ∞-loop space) =  a fold-to-normal-form correspondence (view = Raw.fold)
```

Set against `two_cells.md`: that note found readings form a **2-category** (1-cells `refines`, 2-cells
`IsLensMorphism`/`view_factors_through_morphism`). An operad is the *multi-input* refinement of that
same picture — where a 2-cell relates two readings (one input each, `L ⟹ M`), an operad's `∘ᵢ` is the
**multicategory** structure: arrows with many inputs, composed at slots. The 2-category is the arity-1
shadow; the operad is the full arity grading. This is the new datum (below).

## THE REVELATION (collapse + forcing + spine)

**Collapse — the operad axioms ARE the fold's `raw_initial` coherence, not new axioms.** The three
operad axioms (associativity of `∘ᵢ`, equivariance, unit) are not posited; they **fall out** of "the
fold is the unique structure-preserving map out of the generating distinguishing":
- *Associativity* of `∘ᵢ` is `Raw.fold_slash` (`Theory/Raw/Fold.lean:37`, PURE): folding a slash node
  equals combining the folds of its parts — and this is exactly "substitute-then-evaluate =
  evaluate-the-substituted." The associativity of operadic composition (substitute into slot `i` of
  slot `j` = the two orders agree) is the same homomorphism propagated by `Raw`-induction.
- *Uniqueness/well-definedness* of the composite is `raw_initial` (`SemanticAtom.lean:412`, PURE) +
  `dhom_unique_pointwise` (`UniversalDistinguishing.lean:103`, PURE): there is **exactly one** fold out
  of `Raw` into any carrier, so the operadic composite an algebra computes is forced — the coherence
  the operad axioms demand is the initiality the calculus already proves. This is the *same*
  `raw_initial`/`dhom_unique_pointwise` that `category_theory.md` named the catamorphism and
  `two_cells.md` named the unique 2-cell out of `Raw`. **The operad's coherence and the calculus's
  initiality are one theorem, read at all arities.**

**Forcing — arity 2 is the generating arity; higher arities reduce to nested binaries.** An operad is
generated by its binary operations only when higher arities are recoverable by composition — this is
exactly the calculus's arity-forcing. `CombinatorialArity.arity_2_unique_via_k_ge_3_vacuous`
(`Theory/Atomicity/CombinatorialArity.lean:180`, **5/0 PURE**): for every `k ≥ 3`, no `k`-ary
`rel`-term is reachable over a `Fin 2` base (`no_reachable_rel`, by pigeonhole) — the `≥3`-ary
operations collapse, and `k=0,1` are degenerate, so **`k=2` is the unique non-vacuous generating
arity**. In operad language: the calculus's operad is **binary-generated** (the little-disks /
associative operad's `𝒪(2)` generates), and the "operations of every arity `n`" are *forced* to be
nested binaries — the operad is freely generated by `𝒪(2) = Raw.slash`. This is the forcing the thesis
predicted: the arity grading is real, but the *generators* sit at arity 2, the rest is `Raw.fold`.

**Spine — Assoc/Comm/Lie are the q=±1 readings of one fold; A∞ coherence is Catalan.**
- *The associative operad* = the strict linear `Raw.fold` (no symmetry quotient): composition trees
  read with order kept.
- *The commutative operad* = the **`slash_comm` symmetric quotient** (`Theory/Raw/Slash.lean:40`,
  PURE): `a/b = b/a`, the `q=+1` directionless pole — inputs unordered. This is `two_cells.md`'s
  naturality/symmetry shape at every arity.
- *The Lie operad* = the **antisymmetric `q=−1` pole**: `lie_theory.md`'s bracket `[X,Y]=XY−YX`
  (`Mat2Bracket.bracket`, `bracket_antisymm` `Mat2Bracket.lean:76`, **10/0 PURE**), the same sign-fold
  as `det`/`∂`/ℤ's sign; the operad's Jacobi relation is `Mat2Bracket.jacobi` (`:118`), the
  graded-Leibniz `q=−1` cyclic cancellation `two_cells.md`/`lie_theory.md` already located. So the
  three classical operads are **one fold read at its three symmetry poles** — `q` keeping order
  (Assoc), `q=+1` forgetting it (Comm), `q=−1` signing it (Lie). No three primitives; one fold, the
  `q=±1` direction axis.
- *A∞ coherence is grounded by Catalan.* The Stasheff associahedron `Kₙ` (the polytope whose
  cells are the ways to re-associate `n` binary products) is counted by **Catalan numbers**, and the
  repo HAS them: `Catalan.catalan` with the recursion `Cₙ₊₁ = Σᵢ Cᵢ·Cₙ₋ᵢ`
  (`catalan_recursion_3..7`, `Combinatorics/Catalan.lean:63–92`, **17/0 PURE**) — *literally* the
  count of binary-tree shapes / parenthesizations on the distinguishing's dyadic substrate (the file's
  own docstring: "dyadic-tree shapes with n internal nodes", "balanced parenthesizations"). The
  Catalan **convolution recurrence is the operadic composition law on the free binary operad** (split a
  tree at the root into a left subtree of `i` and a right of `n−i`), so the associahedron's coherence is
  not asserted — the count that controls A∞ is a closed ∅-axiom theorem. The `q=+1` convergence of the
  coherence tower (E∞, all higher coherences present) is the same converging pole as `golden_is_converge`;
  May recognition (E∞ ⟺ ∞-loop space) is a `view = Raw.fold` fold-to-normal-form correspondence.

## VALIDATE — verdict

**PREDICTION (consolidation), with one new structural datum, two built operads, and one located break.**
Like `lie_theory.md`/`representation.md`, operads introduce **no new primitive** and consolidate four
prior files (`category_theory.md`, `two_cells.md`, `lie_theory.md`, `curry_howard.md`) under the two
standing invariants — but the field adds a genuinely new datum: the **arity grading**, the multicategory
generalization of `two_cells.md`'s 2-category.

- **Leg 1 — operad = the fold made arity-graded; axioms = `raw_initial` coherence. BUILT ∅-axiom (the
  legs).** Composition = `Raw.fold` (`Fold.lean:22`); associativity = `Raw.fold_slash` (`:37`, 6/0
  PURE); unit = `Raw.fold_a` (`:30`); well-definedness/uniqueness = `raw_initial` (PURE) +
  `dhom_unique_pointwise` (6/0 PURE). The operad's coherence is the calculus's initiality, verbatim.
- **Leg 2 — arity 2 is forced as the generating arity. BUILT ∅-axiom.**
  `CombinatorialArity.arity_2_unique_via_k_ge_3_vacuous` (`:180`, **5/0 PURE**): the arity-graded
  signature `rel : (Fin k → Raw k) → Raw k` (`:90`) is non-vacuous only at `k=2`, so the calculus's
  operad is binary-generated — the operad's higher arities reduce to nested `Raw.slash`. This is the
  sharpest in-repo grounding of the thesis: the arity-graded operations *exist as a type family* and
  the generating arity is *proven* to be 2.
- **Leg 3 — Assoc/Comm/Lie = the q=±1 readings of the fold. BUILT ∅-axiom (Comm + Lie poles).** Comm =
  `slash_comm` (`Slash.lean:40`, 11/0 PURE, the `q=+1` symmetric quotient); Lie = `bracket_antisymm`
  (`Mat2Bracket.lean:76`, 10/0 PURE, the `q=−1` antisymmetric pole) + `jacobi` (`:118`). The associative
  operad is the strict fold. Three operads, one fold, the `q=±1` axis.
- **Leg 4 — A∞ associahedron coherence = Catalan. GROUNDED ∅-axiom.** `Catalan.catalan_recursion_3..7`
  (`Catalan.lean:63–92`, **17/0 PURE**) is the operadic composition recurrence on free binary trees =
  the associahedron face-count. The coherence that A∞ carries-as-data is counted by a closed theorem.

**The located break (the genuinely missing object).** The **named `Operad` / `arity-composition ∘ᵢ` /
equivariance / `A∞`/`E∞` / `MayRecognition` object is ABSENT.** Grep-confirmed: the only in-repo
`operad` occurrences are in `Algebra/GRA/` (`HigherAlgebra.lean`, `LensIsoCapstone.lean`,
`Enrichment.lean`), where "operad" names an **operad-*level* grade reading** — `Operad(level)` for "Eₙ
operad levels / chromatic heights" in the (2,3)-GRA universality framework — NOT a genuine operad with
a composition map `∘ᵢ : 𝒪(m)×𝒪(n) → 𝒪(m+n−1)`. `operadLens` is *definitionally* `gradeLens`
(`LensIsoCapstone.lean:151`); `GRA23_HigherAlgebra` (`HigherAlgebra.lean:88`) models "operad level" as
`Nat` with `oplus = otimes = (+)` and `ha_reach` (`:72`) = the (2,3) reachability — a grade arithmetic,
not an operad's substitution structure. So the GRA "operad" is honest as a *reading of operad level*
but is **not** the arity-graded composition object the thesis is about; the genuine
`∘ᵢ`/equivariance/A∞ structure is built only at the *leg* level (fold, arity-forcing, the q=±1 operads,
Catalan), with the named bundle absent — the abelian/higher-categorical twin of `two_cells.md`'s missing
horizontal-composition/interchange packaging and `lie_theory.md`'s missing tangent `ε`.

**Net verdict: PREDICTION.** Every load-bearing leg is a closed ∅-axiom theorem (`Raw.fold_slash`,
`raw_initial`, `dhom_unique_pointwise`, `arity_2_unique_via_k_ge_3_vacuous`, `slash_comm`,
`bracket_antisymm`/`jacobi`, `catalan_recursion_n`); the operad axioms = the fold coherence, the
generating arity = 2 (forced), the three operads = the q=±1 readings, A∞ = Catalan. The new datum is the
**arity grading = the multicategory above the 2-category** (`two_cells.md` is its arity-1 shadow). The
break is the **named `∘ᵢ`/equivariance/A∞/E∞ object**: the GRA "operad" is a grade *reading*, not the
substitution structure — a precisely-located absence, not a hand-wave. 82-flavoured decomposition;
operads EXTEND by consolidation, with the named operad-composition bundle as the located break.

## Note for the technique — does operads touch model v7.1?

**No new invariant; one frame refinement (arity grading) + EXTEND.** The two invariants (character
arrow, q=±1 residue) and four axes absorb operads whole:

> **An operad is the calculus's `Raw.fold` composition made ARITY-GRADED — the multicategory above
> `two_cells.md`'s 2-category of readings.** Where a 2-cell relates two readings (one input,
> `view_factors_through_morphism`), an operad's `∘ᵢ` is the many-input composition; the operad axioms
> (associativity/equivariance/unit) are the fold's `raw_initial`/`dhom_unique_pointwise` coherence, the
> *same* initiality `category_theory.md`/`curry_howard.md` name. The generating arity is **forced to 2**
> (`arity_2_unique_via_k_ge_3_vacuous`): the operad is binary-generated, higher arities = nested
> `Raw.slash`. The three classical operads are **one fold at its q=±1 poles** — Assoc (order kept),
> Comm (`slash_comm`, q=+1), Lie (`bracket_antisymm`, q=−1, `lie_theory.md`). A∞ coherence is the
> associahedron, **counted by Catalan** (`catalan_recursion_n`, the free-binary-operad composition
> recurrence). The located break is the **named `Operad`/`∘ᵢ`/equivariance/A∞/E∞ bundle**: the only
> in-repo "operad" is an operad-*level grade reading* in GRA (`operadLens = gradeLens`), not the
> substitution structure — the multicategory packaging is the open leg, twin of `two_cells.md`'s missing
> interchange and `lie_theory.md`'s missing `ε`.

So model v7.1's interior is unchanged; the frame gains the observation that **the 2-category of readings
is the arity-1 truncation of a multicategory/operad** — arity grading is a coordinate the calculus's
composition already carries (the `k`-ary `rel`, with `k=2` forced), not a new axis.

## Verified Lean anchors (file:line — all grep + scan-verified this session; all PURE)

| Leg | Theorem / def (file:line) | Status |
|---|---|---|
| ★ composition = the catamorphism (the fold) | `Theory/Raw/Fold.lean:22` `Raw.fold`; `:30` `Raw.fold_a` (unit) | **PURE (6/0)** ✓ |
| ★ ∘ᵢ-associativity = fold homomorphism | `Theory/Raw/Fold.lean:37` `Raw.fold_slash`; `:67` `fold_slash_iff`; `:87` `fold_slash_rel` | **PURE (6/0)** ✓ |
| ★ composite is unique = initiality | `Lens/Foundations/SemanticAtom.lean:412` `raw_initial` | **PURE** ✓ |
| ★ only one fold out of Raw (coherence) | `Lens/Foundations/UniversalDistinguishing.lean:103` `dhom_unique_pointwise` | **PURE (6/0)** ✓ |
| ★ arity-graded ops: `k`-ary `rel : (Fin k → Raw k) → Raw k` | `Theory/Atomicity/CombinatorialArity.lean:90` `Raw (k)`; `:97` `Reachable` | def (∅-axiom) ✓ |
| ★ arity 2 forced as the generating arity (k≥3 vacuous) | `Theory/Atomicity/CombinatorialArity.lean:115` `reachable_only_object`; `:154` `no_reachable_rel`; `:180` `arity_2_unique_via_k_ge_3_vacuous` | **PURE (5/0)** ✓ |
| ★ generating binary op = the distinguishing | `Theory/Raw/Slash.lean` `Raw.slash` (see `API.lean:33`) | def (∅-axiom) ✓ |
| ★ commutative operad = symmetric quotient (q=+1) | `Theory/Raw/Slash.lean:40` `Raw.slash_comm` (`x/y = y/x`) | **PURE (11/0)** ✓ |
| ★ Lie operad = antisymmetric bracket (q=−1) + Jacobi | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:66` `bracket`; `:76` `bracket_antisymm`; `:101` `tr_bracket_zero`; `:118` `jacobi` | **PURE (10/0)** ✓ |
| ★ A∞ associahedron coherence = Catalan (op composition recurrence) | `Lib/Math/Combinatorics/Catalan.lean:26` `catalan`; `:63–92` `catalan_recursion_3..7` (`Cₙ₊₁ = Σ Cᵢ·Cₙ₋ᵢ`) | **PURE (17/0)** ✓ |
| algebra over an operad = a Lens-image; A∞ witness-carrying normal form | `Lib/Math/Algebra/Group/FreeReduction.lean:237` `proj_val_eq_iff`; `:191` `freeReduce_idempotent`; `:264` `free_group_quotient_no_quot` | **PURE (26/0)** ✓ (cross-frame) |
| 2-cell = arity-1 truncation of the operad's ∘ᵢ | `Lens/Compose/Morphism.lean:29` `IsLensMorphism`; `:37` `view_factors_through_morphism`; `:60` `refines_of_morphism` | **PURE (3/0)** ✓ (cross-frame) |
| cross-frame | `two_cells.md` (2-category), `lie_theory.md` (Lie operad/`Mat2Bracket`), `category_theory.md`/`curry_howard.md` (fold = catamorphism/recursor) | prior, ∅-axiom ✓ |

Scan tallies (`tools/scan_axioms.py`, this session): `Theory.Raw.Fold` 6/0; `Theory.Raw.Slash` 11/0
(`slash_comm` PURE); `Theory.Atomicity.CombinatorialArity` 5/0; `Lens.Foundations.UniversalDistinguishing`
6/0 (`dhom_unique_pointwise` PURE); `Lens.Foundations.SemanticAtom` — module 11/23 but `raw_initial`
**individually PURE**; `Mat2.Mat2Bracket` 10/0; `Combinatorics.Catalan` 17/0;
`Algebra.Group.FreeReduction` 26/0; `Lens.Compose.Morphism` 3/0.

## Dropped / flagged (honest — NOT cited as anchors)

- **The named `Operad` / `arity-composition ∘ᵢ` / equivariance / `A∞` / `E∞` / `MayRecognition`
  object — ABSENT.** Grep-confirmed: the only in-repo "operad" is `Algebra/GRA/`'s operad-*level grade
  reading* (`operadLens` is definitionally `gradeLens`, `LensIsoCapstone.lean:151`; `GRA23_HigherAlgebra`
  `HigherAlgebra.lean:88` models "operad level" as `Nat` with `+`/`+` and (2,3) reachability `ha_reach`
  `:72`). This is honest as a reading of operad *level* but is **not** the substitution structure
  `∘ᵢ : 𝒪(m)×𝒪(n)→𝒪(m+n−1)` with equivariance; it is NOT cited as an anchor for the composition thesis.
  (Caveat on its scan: `scan_axioms.py` mis-resolves names across the `HigherAlgebra`/`Universality`
  namespace split in that file, reporting only 5/0 on the resolvable names; the file header asserts "0
  sorry, ∅-axiom". Cited only with this caveat, and only as the *level reading*, not the operad object.)
- **The genuine `∘ᵢ` composition map and Σₙ-equivariance as Lean objects** — not built. Grounded only
  at the leg level: `Raw.fold`/`Raw.fold_slash` (the binary-composition coherence) + the q=±1 readings
  + Catalan (the coherence count). The arity-`n`-to-arity-`(m+n−1)` substitution map is the open target.
- **A∞/E∞ as homotopy-coherent objects** — absent. The *coherence count* (associahedron = Catalan,
  17/0) is built and the witness-carrying pattern (`FreeReduction`, 26/0) is the right shape, but no
  `Aoperad`/`Eoperad`/homotopy-coherence tower object exists. Same `Real213`/colimit-corner cap as
  `two_cells.md`'s isotopy/interchange and `lie_theory.md`'s tangent `ε`.
- **May recognition principle (E∞-algebra ⟺ ∞-loop space)** — prose-only. The `view = Raw.fold`
  fold-to-normal-form shape is the right analogue, but the loop-space side has no in-repo object (the
  same ambient-space absence `two_cells.md` Shape 3 located).

### Verified buildable witness (named, not asserted)
A **free binary operad composition-at-root** theorem is buildable ∅-axiom from existing PURE legs:
state `splitAtRoot : Raw.slash x y h ↦ (x, y)` and prove the operadic composition law
`fold(slash x y) = combine (fold x)(fold y)` is the Catalan-convolution split — this is `Raw.fold_slash`
(`:37`) re-read as "split a composition tree at the root into subtrees of arity `i` and `n−i`," matching
`catalan_recursion_n` (`Cₙ₊₁ = Σᵢ Cᵢ·Cₙ₋ᵢ`). Both halves are already closed PURE; the witness is the
named bridge theorem `fold_split = catalan_convolution` (a `decide`-checkable equality on the tabulated
range), the operadic-composition twin of the associahedron count. Not built this session; named as the
concrete promotion target.

### Cross-frame
`two_cells.md` (the 2-category of readings = the operad's arity-1 truncation; `view_factors_through_morphism`,
`dhom_unique_pointwise`); `lie_theory.md` (the Lie operad = `Mat2Bracket` antisymmetric q=−1 pole, Jacobi
= graded-Leibniz); `category_theory.md` (`raw_initial`/`fold` = initial object + catamorphism — the operad
coherence is this initiality); `curry_howard.md`/`cut_elimination.md` (the fold = the recursor/cut, the
composition the operad grades); `golden_ratio.md`/SYNTHESIS `golden_is_converge` (E∞ = the q=+1 converging
coherence tower).
