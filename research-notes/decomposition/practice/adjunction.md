# Decomposition: adjunction / monad — the calculus's META-structure made explicit

*META-decomposition, per `../README.md` (model v4): the calculus has been saying "readings form a
category" since batch 3 (they compose in series — entropy; form composition-closed families — groups;
form adjoint/order-reversing pairs — Galois). This entry makes that explicit and asks the LEVERAGE
question: does naming "readings = a category with adjunctions and monads" **PREDICT** where universal
constructions must live, or does it only re-organize what the other entries already found?*

This entry is META — its object is not a piece of classical mathematics but **the decomposition
calculus itself**. The three batch-4 hypotheses to derive:

1. `galois.md`'s order-reversing Galois connection is the **antitone special case** of a general
   **adjunction `F ⊣ G`** between reading-families.
2. Composing an adjoint pair gives a **monad** `T = G∘F` on readings; the closure operator `clo` from
   `galois.md` **IS** that monad's idempotent shadow (`T² → T` collapsed to `T∘T = T`).
3. The calculus's universal constructions (initiality of Raw, the residue's self-application) are this
   category-of-readings' **(co)limits / (co)algebras**.

## The decomposition (C / Reading / Residue) — applied to the calculus

- **Construction `C`** — here `C` is *the collection of readings itself*. The calculus's own objects.
  A reading is `Lens`-shaped (`Lens/LensCore.lean`: `structure Lens` = `(base_a, base_b, combine)`,
  with `Lens.view = Raw.fold` the catamorphism into `α`).

- **Reading `L`** — the *organizing* reading laid over that collection is **"how do readings relate?"**
  Three arrows, each already proven:
  - **refinement** `Lens.refines L M := ∀ x y, L.equiv x y → M.equiv x y` (kernel containment) —
    `refines_refl` + `refines_trans` make this a **thin category** (preorder) on readings.
  - **iso** `LensIso L M` (mutual refinement = kernel coincidence, `lensIso_iff_kernel_eq`) —
    `lensIso_refl`/`symm`/`trans` make the isos a **groupoid** (the core of the category).
  - **adjunction** `Fix ⊣ Inv` between two refinement-ordered reading-lattices —
    `Order/GaloisConnection.lean`'s `gc`, the antitone case run with one order flipped (`galois.md`).

- **Residue** — what the organizing reading forces but does not capture is the **closure gap**: the
  monad `T = G∘F` is not the identity off the closed elements. `Residue = clo a` vs `a`. The residue
  *vanishes exactly on the algebras* (closed/fixed elements), which is why a bijection (fundamental
  theorem) appears there and an adjunction-not-iso appears elsewhere.

## Re-seeing — readings as a category with adjunctions and monads

```
   category of readings   =  ⟨ readings | the relating-arrows refines / LensIso / Fix⊣Inv ⟩

   objects                =  Lens α        (a reading; Lens.view = Raw.fold = catamorphism)
   thin-category arrows   =  Lens.refines  (refines_refl, refines_trans)            [preorder]
   groupoid core          =  LensIso       (lensIso_refl/symm/trans)                [iso part]
   adjunction  F ⊣ G      =  gc : leB (f a) b ↔ leA a (g b)
                             unit  η : a ≤ g(f a)   (gc_unit)
                             counit ε : f(g b) ≤ b  (gc_counit)
                             triangle identities    (gc_fgf : f∘g∘f = f,  gc_gfg : g∘f∘g = g)
   monad  T = G∘F         =  clo := g ∘ f
                             η (unit)         =  clo_extensive  (a ≤ clo a)
                             T monotone       =  clo_monotone
                             μ : T² → T       =  clo_idempotent (clo (clo a) = clo a)   ← T∘T = T
   the algebras (T-fixed) =  closed elements (closed_iff_image, gc_le_closed)
   monad composition      =  gc_comp (adjoint pairs compose → T's compose)
```

The Galois connection of `galois.md` is **one antitone arrow in this category**; the general
**covariant adjunction** `F ⊣ G` is the same `gc` skeleton with no order flipped. The two triangle
identities `gc_fgf`/`gc_gfg` are *exactly* a categorical adjunction's triangle identities (pointwise,
no `funext`). And `clo = g∘f` with `clo_extensive` (unit) + `clo_idempotent` (μ: `T²=T`) **is a
monad** — specifically the idempotent monad an adjunction always generates. Hypothesis 2 is
**confirmed structurally**: `clo` is not merely *related to* a monad, `clo`'s three laws *are* the
monad laws of `T = G∘F`, with `clo_idempotent` the multiplication collapsed by idempotence.

The third leg — initiality / self-application as (co)limits — also lands:
- **Initial object** of the category-of-constructions: `raw_initial` (`Lens/Foundations/SemanticAtom.lean`)
  proves `Raw` is initial — for every `HasDistinguishing α` there is a **unique** morphism
  `universalMorphism α : Raw → α` (`universalMorphism_unique`), and that unique morphism **is the
  catamorphism** `Raw.fold` (`Lens.view`). So "read a construction through a reading" = "the unique
  arrow out of the initial object" = the catamorphism. Initiality and the calculus's read-operation
  are one thing.
- **Endofunctor / free-monad shadow**: `foldRaw : Raw → Raw` (`Theory/Raw/Endomorphic.lean`,
  `= Raw.fold` at `α := Raw`) is the **endo-reading** `T : Raw → Raw`; `OnLens.lean`'s
  `universalMorphism (Lens Bool) : Raw → Lens Bool` is the construction *re-entering its own reading
  type* — "no meta-hierarchy, Lens is another instance" (Note 53). This is the residue's
  self-application as an **endofunctor on the category**, the (co)algebra side.

## LEVERAGE — does making "readings = a category with adjunctions/monads" PREDICT?

**Honest verdict: ORGANIZING with one genuine, narrow PREDICTION — not a re-skin, not a broad new
generator.** Three things, ranked by how much they pay.

**(a) Confirmed structural collapse (organizing, but real).** "Galois connection = antitone
adjunction" and "`clo` = the adjunction's idempotent monad `T=G∘F`" are not re-labels — they are
*provable identities of laws*: `gc_unit`=η, `gc_counit`=ε, `gc_fgf`/`gc_gfg`=triangle identities,
`clo_extensive`+`clo_idempotent`=monad unit+μ. The repo proved the monad *before* anyone called it
one (`clo_idempotent`, `gc_idempotent_closure`). That is the calculus's standing payoff (collapse),
not new leverage.

**(b) The one genuine PREDICTION: "every adjoint reading-pair generates a closure, and the
correspondence/bijection lives exactly on its algebras."** Naming the monad tells you *where to look
for the universal property without re-deriving it per instance*: given **any** two refinement-ordered
reading-families joined by a `gc`, the fundamental-theorem-style bijection **must** appear on
`closed_iff_image` / `gc_le_closed` (the `T`-fixed points), and nowhere else. This predicted the
`refines ⟺ divides` ⟷ lcm/gcd lattice bijection (`galois.md`) as *the same shape* as Galois, and it
predicts that **any future adjoint pair the calculus builds (e.g. a syntax/semantics reading-pair, a
coarsen/refine pair) will carry its bijection on its closure** — checkable, falsifiable, not a
re-description. `gc_comp` extends the prediction: closures **compose**, so a chain of adjoint readings
has a *composite* closure whose algebras are the intersection — a structural forecast.

**(c) Where it does NOT yet pay (honest miss / open).** The strong CT slogans the META-framing
*invites* are **not** discharged in the repo:
- *"Every endo-reading has a free monad"* — **FALSE / unavailable here.** `foldRaw : Raw → Raw` is an
  endo-fold, but there is **no** `Lens.bind`, no Kleisli composition, no general free-monad
  construction (grep: `def map|def bind|Lens.comp` in `LensCore` → **no matches**). The only monad the
  repo actually has is the *idempotent* closure monad from adjunctions; the general "free monad of an
  endofunctor" is conceptual-only. The META-framing **predicts** it should exist; the repo does **not**
  ground it. Flagged, not asserted.
- *"Every construction has an initial reading"* — partially. `raw_initial` gives the initial *object*
  (Raw) and the unique catamorphism, which is strong; but a general (co)limit calculus on readings
  (products `iProdLens`, joins `iJoinLens` exist in `Lens/Lattice/` — verified by file presence, not
  audited here) is not packaged as "the category-of-readings has all (co)limits." So initiality is
  real; completeness is conceptual.

**Net:** the META-structure is **mostly organizing** (it tidies entropy/groups/Galois under one
"category of readings" roof and *confirms* the monad was already proven), with **one real leverage
claim** — the closure-monad localizes every adjoint-pair's universal property onto its algebras,
predicting *where* future bijections live. It is **not** the broad generator CT's slogans promise:
the free-monad prediction is a genuine **miss** (no `bind` in the repo), and that miss is the honest
boundary of the framing.

## Note for the technique — should the README promote "readings form a category with adjunctions/monads" to a core principle?

**Recommendation: promote it as a *descriptive* core principle (it unifies batches 3–4 and is
fully Lean-grounded), but DO NOT advertise it as a *predictive* engine beyond the one claim it earns.**

What it earns the right to say:
- **Readings form a category** — objects = `Lens`, arrows = `Lens.refines` (thin category,
  `refines_refl/trans`), with a groupoid core (`LensIso`, `lensIso_refl/symm/trans`). *Grounded.*
- **Adjoint reading-pairs generate idempotent monads** — `F ⊣ G` (`gc`) ⟹ `T = clo = G∘F` with
  `clo_extensive` (η) + `clo_idempotent` (μ, `T²=T`). The antitone case is Galois; the covariant case
  is the same `gc`. *Grounded.*
- **PREDICTION (the load-bearing addition):** *the universal property of any adjoint reading-pair lives
  on its closure's algebras* (`closed_iff_image`/`gc_le_closed`), and closures compose (`gc_comp`).
  This is the one thing the framing predicts that a per-instance write-up would not hand you for free.
- **Initiality = the read-operation:** the catamorphism `Lens.view = Raw.fold` IS the unique arrow
  out of the initial object `Raw` (`raw_initial`, `universalMorphism_unique`). *Grounded — and it
  retro-explains why "read C through L" was always the same primitive.*

What it must **not** claim (the fog guard): "every endo-reading has a free monad" / "the category has
all (co)limits" — **the repo has no `bind`, no Kleisli, no free-monad construction**; only the
idempotent closure monad is real. Promoting the principle with those slogans attached would be
exactly the "abstract nonsense" the README's revelation-rule forbids. Promote the *grounded* shape and
the *one* prediction; record the free-monad/completeness slogans as **open Lean targets**, not
results.

The deeper META-reading: the calculus *is* a category whose objects are readings and whose deepest
constructions (initiality, the closure monad, the residue's self-application endofunctor) are the
standard universal constructions — but the repo grounds the **idempotent/closure** corner of that
category (where residues *settle*, `q=+1`), not the **free/non-idempotent** corner (where they would
*grow*). That asymmetry is itself a finding: the calculus's category is, so far, a category of
**residues that converge** — the same `q=+1` pole `galois.md` already noted for `clo`.

## Verified Lean anchors (all grep-checked, ∅-axiom-style)

Adjunction + monad (the closure monad `T = G∘F`):
- `Lib/Math/Order/GaloisConnection.lean`: `gc_unit` (η), `gc_counit` (ε), `gc_monotone_f`,
  `gc_monotone_g`, `gc_fgf` (`f∘g∘f=f`), `gc_gfg` (`g∘f∘g=g`) — triangle identities; `clo` (def, `g∘f`),
  `clo_extensive` (unit), `clo_monotone`, `clo_idempotent` (μ: `clo(clo a)=clo a`, `T²=T`);
  `gc_unique_right`; `mulDiv_gc` (concrete witness `(·*p) ⊣ (·/p)` on `Nat`)
- `Lib/Math/Order/GaloisConnectionComposition.lean`: `gc_comp` (adjoints/monads compose),
  `closed_iff_image`, `gc_idempotent_closure`, `gc_le_closed` (the **algebras** = closed elements)

Category of readings:
- `Lens/LensCore.lean`: `structure Lens`, `Lens.view` (= `Raw.fold`, the catamorphism), `Lens.equiv`,
  `Lens.refines` (def), `refines_refl`, `refines_trans` (thin category)
- `Lens/Unified.lean`: `LensIso` (def), `lensIso_refl`, `lensIso_symm`, `lensIso_trans` (groupoid),
  `lensIso_iff_kernel_eq` (iso = kernel coincidence)

Initiality + the endo-reading (co)algebra side:
- `Lens/Foundations/SemanticAtom.lean`: `raw_initial` (Raw is initial), `universalMorphism` (the
  unique arrow = catamorphism), `universalMorphism_unique`, `universalMorphism_slash` (homomorphism law)
- `Theory/Raw/Fold.lean`: `Raw.fold` (def, catamorphism), `Raw.fold_slash` (the fold homomorphism)
- `Theory/Raw/Endomorphic.lean`: `foldRaw` (= `Raw.fold` at `α:=Raw`, the **endo-reading** `T:Raw→Raw`),
  `foldRaw_slash`
- `Lens/Compose/OnLens.lean`: `universalMorphism (Lens Bool) : Raw → Lens Bool` (self-application —
  the construction re-entering its own reading type; "no meta-hierarchy")

## Dropped / conceptual-only (honest)

- **`Lens.bind` / Kleisli / general free monad** — **DO NOT EXIST.** Grep for `def map|def bind|def
  comp|Lens.comp` in `Lens/LensCore.lean` → no matches. The only monad in the repo is the *idempotent
  closure* monad from adjunctions. The CT slogan "every endofunctor has a free monad" is conceptual-
  only — an **open Lean target**, not grounded. (This is the LEVERAGE miss, flagged above.)
- **"Category of readings has all (co)limits"** — `Lens/Lattice/{Join,IndexedJoin}.lean` have
  `iJoinLens`/`iProdLens` (products/joins exist by file presence), but no packaged completeness
  theorem; "every construction has an initial reading" is grounded only as `raw_initial` (the initial
  *object*), not as general (co)limit existence. Conceptual beyond initiality.
- **Covariant (non-antitone) adjunction as a *named* repo object** — the `gc` skeleton is order-
  parametric so the covariant case is the same theorems with no flip, but no file instantiates a
  *covariant* reading-adjunction by name; only the antitone Galois case (`galois.md`) and the `mulDiv`
  numeric witness are concrete. The covariant reading-pair is structurally available, not exhibited.
