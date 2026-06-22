# Frontier: the colimit / ambient-quotient corner — category-theory verdict

**Status**: open-corner assessment (panel memo, 2026-06-22). Mirrors the "constructive wall" panel
that defeated a thought-impossible obstruction by reframing it as an interface defect. Object: the one
genuine recurring absence of the 213 Decomposition Calculus — the **ambient-deformation / colimit
quotient** (knot isotopy in `knots.md`, path homotopy in `fundamental_group.md`), located by
`two_cells.md` at "the un-built `q=−1`/colimit corner + an absent ambient-space construction".

**Verdict (headline): INTERFACE DEFECT, split clean from a residual.** The *quotient-by-a-generated-
equivalence* layer is buildable ∅-axiom right now, as a normal-form type + a terminating reduction —
**the repo already has the pattern built** (`Lens.Unified.LensImage` / `proj_val_eq_iff`) and already
has the termination floor (`no_infinite_descent` / `isPart_wf`). What is *not* a defect, and not part
of the colimit corner at all, is the **ambient 3-space construction** (an embedding `S¹↪S³`, a smooth
isotopy): that is missing input data, not a missing categorical primitive. Once the move-set is given
as data, the quotient is ∅-axiom. The colimit/`q=−1` corner is therefore an **interface defect**; the
"ambient space" is a separate, honestly-absent *modelling* leg, not an obstruction to the quotient.

---

## 1. What the missing primitive IS, categorically

The calculus builds the `q=+1` corner: the **closure monad** `clo = g∘f` from an adjoint pair
(`GaloisConnection.lean`: `clo`, `clo_extensive`, `clo_idempotent`, `gc_fgf`/`gc_gfg`), and
**equivalence-via-kernel** (`Unified.lean`: `LensIso L M ↔ ∀ x y, L.equiv x y ↔ M.equiv x y`,
`lensIso_iff_kernel_eq`). A `Lens` kernel is `L.equiv x y := L.view x = L.view y` (`LensCore.lean:48`)
— an equivalence that is *already* a function-fibre.

The missing thing is the dual: a **coequalizer** — the quotient `Raw / ≈` where `≈` is the smallest
equivalence relation *generated* by a relation `R` (the move-set: Reidemeister/Markov for knots, the
homotopy elementary moves for π₁). Categorically: `coeq(R ⇉ Raw) = Raw / (equivalence-closure of R)`.
This is a colimit, the formal `q=−1` partner of the `q=+1` limit/closure the repo has.

**Is it a Lens kernel after all?** Decisive sub-question. A Lens kernel is the fibre of *some*
`view : Raw → α` the calculus can write. The isotopy/homotopy classes ARE such fibres **iff** there is
a computable invariant `view` that separates exactly the classes — i.e. a *complete invariant* whose
fibres are the classes. For braids the writhe + permutation is incomplete; the Jones/Alexander
invariant is incomplete; no finitely-presented complete invariant for knots is known. So:

- The quotient is **provably expressible as a kernel for any chosen *normal form*** (a confluent,
  terminating reduction to canonical representatives — see §2): then `view := normalForm` and
  `L.equiv x y ↔ normalForm x = normalForm y` is exactly `lensIso_iff_kernel_eq`'s shape, ∅-axiom.
- It is **not** a kernel of any *cheap character* the calculus already writes (writhe, holonomy
  product, abelianization) — those have strictly coarser fibres (this is exactly `knots.md` Gap, and
  `fundamental_group.md` leg 4: the homotopy relation is finer than the holonomy kernel).

So the corner is "kernel of a normal-form map" — present in *principle*, absent only as the *specific
move-set datum*. That is the defect/obstruction fork, and it resolves toward defect.

## 2. The decisive test — carry the equivalence witness AS DATA (mirroring modulus-as-data)

The wall fix carried the **modulus** as data (Real213 = approximant-sequence-with-modulus, not a
Cauchy `Quot`). The exact analogue here:

> **quotient ≔ the type of normal forms + a proof that the reduction is terminating (and the chosen
> reduction is confluent → unique normal form).** A class is *a construction PLUS an explicit
> reduction-path to its canonical representative* — never a `Quot`.

The repo **already ships this pattern**, ∅-axiom, in `Lens/Unified.lean`:

```
  LensImage L := { a : α // ∃ r : Raw, L.view r = a }      -- the quotient as a Σ-type, no Quot.sound
  LensImage.proj L r := ⟨L.view r, r, rfl⟩                  -- PURE substitute for Quot.mk
  proj_val_eq_iff : (proj L x).val = (proj L y).val ↔ L.equiv x y   := Iff.rfl   -- = the sound-rule, PURE
```

`proj_val_eq_iff` is `Quot.sound`'s computational content with **no axiom** (it is `Iff.rfl`): two
representatives are identified iff they share the `view`. The docstring of `Unified.lean` states this
explicitly — `LensImage` is "the quotient `Raw / L.equiv` as a Σ-type … No `Quot.sound` required."
This is the modulus-as-data move, already made, for kernels. The colimit corner needs only to supply
`view = normalForm` for a *generated* relation rather than a function-fibre.

**Termination is in hand.** A reduction terminates iff there is a well-founded measure that strictly
drops. The repo has the canonical one: `Lambek.no_infinite_descent` (`Theory/Raw/Lambek.lean:273`) —
no `chain : Nat → Raw` peels at every step, with an *explicit length bound* (`(chain 0).depth + 1`),
backed by `isPart_wf` (`:199`) and `terminal_iff_atom` (`:308`, the descent stops exactly at the
atomic floor). This is the `q=+1` well-founded floor `curry_howard.md` reads as strong normalization.
Any reduction whose move strictly drops a `Nat`-valued measure inherits termination from the same
`Nat`-well-foundedness `descent_chain_drops` uses — no `Classical`, no `WellFounded.fix` over an
undecidable order.

**So the construction sketch (∅-axiom, no Quot.sound, no HIT, no coinduction):**

1. Move-set `R : Word → Word → Prop` given **as decidable data** (Reidemeister/Markov as concrete
   rewrite rules on braid words; for π₁, the elementary homotopy moves on edge-paths).
2. A `Nat`-valued complexity measure `μ` that the *reduction direction* strictly drops to a canonical
   floor (e.g. shortlex on words; for the free π₁-on-a-graph case, free-reduction length — which is
   genuinely confluent and terminating, the classical Nielsen normal form).
3. `normalForm : Word → Word` = iterate the reduction; terminates by the `no_infinite_descent`
   pattern (μ drops, `Nat` well-founded). Confluence (local, then global via Newman, which needs only
   termination + local confluence — both finitary, decidable here) gives uniqueness.
4. `Class := { w // ∃ v, normalForm v = w }` (the `LensImage` shape); `equiv x y ↔ normalForm x =
   normalForm y` (the `proj_val_eq_iff` shape, `Iff.rfl`); `lensIso_iff_kernel_eq` then certifies it
   is a genuine 213 equivalence-arrow. The 2-cell layer (`view_factors_through_morphism`,
   `IsLensMorphism`) gives the functoriality of invariants out of it for free.

This is achievable ∅-axiom **wherever a confluent terminating reduction exists**.

## 3. Honest verdict — where it IS a defect, where it ISN'T

**(a) Where the reduction is confluent + terminating → INTERFACE DEFECT, buildable now.**
- **π₁ of a graph / free group** (the bulk of `fundamental_group.md`'s loop algebra): free reduction
  (cancel `xx⁻¹`) is confluent and terminating (length strictly drops). Normal form = reduced word.
  ∅-axiom via `LensImage` + `no_infinite_descent`. **This is a defect, fully buildable.** The repo
  already has the loop *word* group (`holonomy_append`) and the abelianization step (`commSet`,
  `derived_S3_step1`); the missing homotopy quotient on a graph is exactly free reduction — a clean
  defect. Repo pieces in hand: `LensImage`/`proj_val_eq_iff` (the quotient-as-Σ), `no_infinite_descent`
  (termination), `lensIso_iff_kernel_eq` (kernel certification), `refines`/`view_factors_through_
  morphism` (functorial invariants out).
- **Braid groups `Bₙ`** (the EXTEND half of `knots.md`): the braid relations are confluent under a
  Garside/greedy normal form (classical, terminating). `Bₙ`-as-Σ-of-normal-forms is ∅-axiom by the
  same recipe. Defect.

**(b) Where it is NOT a defect — two honest residuals, neither a colimit-primitive obstruction:**
- **The ambient 3-space is missing INPUT, not a missing primitive.** Knot isotopy needs an embedding
  `S¹↪S³` and a smooth ambient isotopy — geometric *data* the calculus has never been given (it builds
  `Real213` cuts, not embeddings). This is not the colimit corner; it is an un-modelled object. The
  *quotient machinery* would consume a move-set if handed one; the move-set itself (Reidemeister) is a
  theorem *about* `S³`, not derivable inside the calculus. So "build `S³`" is open modelling work,
  orthogonal to the colimit question — and correctly so: this is the part `two_cells.md` called "an
  absent ambient-space construction", and it should be *unbundled* from the colimit verdict.
- **Knots specifically (full knot equivalence) is not known to have a finite confluent reduction.**
  The word problem for `Bₙ` is solvable (Garside) and braid-isotopy is fine, but the Markov-move
  quotient onto *knot types* has no known terminating confluent normal form (this is a genuine open
  problem in knot theory, not a 213 defect). Here the data-carrying reframing **does not auto-succeed**
  — but the failure is the *absence of a known normal form*, NOT a need for `Quot.sound`/HIT. If a
  confluent terminating system were supplied, the ∅-axiom construction goes through unchanged. So even
  this is "missing data / missing math", not "irreducibly needs a non-constructive principle".

**What is genuinely NOT needed (the wall-defeat parallel):** no `Quot.sound` (replaced by
`proj_val_eq_iff : … := Iff.rfl`), no HIT (the class is a Σ-type of normal forms, a 0-type — the
calculus's `funext`-free 1-categorical ceiling is *exactly right* here, no higher path structure is
being quotiented), no coinduction (the reduction terminates by `no_infinite_descent`, a least-fixed-
point / well-founded fact, never a νF). The colimit corner does not need a *new constructive
principle*; it needs the *move-set as data* + a *terminating reduction*, both of which the calculus's
own `q=+1` termination floor (`isPart_wf`) and its `LensImage` quotient-as-Σ already supply.

## 4. The precise statement of the corner after this assessment

The normal form `⟨C-self-application | reading⟩ ⊕ residue(q=±1)` does cover the colimit/quotient corner
**once the quotient is presented as a kernel of a normal-form reading** — which is ∅-axiom whenever the
generating move-set admits a confluent terminating reduction. The corner splits:

| Sub-case | Confluent terminating normal form? | Verdict |
|---|---|---|
| π₁ of a graph / free group | yes (free reduction, length-drop) | **INTERFACE DEFECT — buildable now** |
| braid group `Bₙ` | yes (Garside/greedy) | **INTERFACE DEFECT — buildable now** |
| full knot type (Markov quotient) | none known | not a 213 defect — *missing math* (no Quot.sound needed if supplied) |
| ambient `S³` embedding/isotopy | n/a (it's input data) | *missing modelling input*, orthogonal to the colimit corner |

The single sentence: **the colimit/ambient-quotient corner is an interface defect — a coequalizer is a
kernel of a normal-form map, and the calculus already ships the ∅-axiom quotient-as-Σ (`LensImage`,
`proj_val_eq_iff = Iff.rfl`) and the termination floor (`no_infinite_descent`/`isPart_wf`) needed to
build it; the only genuinely absent things are (i) a chosen confluent reduction for the harder
move-sets and (ii) the ambient 3-space, and neither is a demand for `Quot.sound`, a HIT, or
coinduction.**

## ∅-axiom repo pieces in hand (grep-verified this session)

| Piece | File:line | Role |
|---|---|---|
| `LensImage` / `LensImage.proj` / `proj_val_eq_iff` | `lean/E213/Lens/Unified.lean:152,157,163` | **quotient-as-Σ, no `Quot.sound`** (`proj_val_eq_iff := Iff.rfl`) — the modulus-as-data analogue, already built |
| `LensFiber` / `fibers_complete` | `lean/E213/Lens/Unified.lean:77,87` | equivalence class as a subtype; classes cover Raw |
| `lensIso_iff_kernel_eq` | `lean/E213/Lens/Unified.lean:64` | certifies "classes of a normal form" = a genuine 213 equivalence-arrow (kernel coincidence) |
| `Lens.refines` / `refines_refl` / `refines_trans` | `lean/E213/Lens/LensCore.lean:90,93,95` | the 1-cell preorder; quotient sits as a `refines`-node |
| `Lens.equiv` (`view x = view y`) | `lean/E213/Lens/LensCore.lean:48` | kernel = function-fibre (the shape `normalForm` must produce) |
| `no_infinite_descent` | `lean/E213/Theory/Raw/Lambek.lean:273` | **termination floor** with explicit length bound — the reduction-terminates ingredient |
| `isPart_wf` | `lean/E213/Theory/Raw/Lambek.lean:199` | well-founded peel relation (qualitative termination) |
| `terminal_iff_atom` | `lean/E213/Theory/Raw/Lambek.lean:308` | descent stops at exactly the canonical floor (normal-form existence pattern) |
| `clo` / `clo_idempotent` / `gc_fgf`/`gc_gfg` | `lean/E213/Lib/Math/Order/GaloisConnection.lean` | the built `q=+1` limit/closure corner — the dual this corner completes |
| `view_factors_through_morphism` / `IsLensMorphism` / `refines_of_morphism` | `lean/E213/Lens/Compose/Morphism.lean:37,29,60` | the 2-cell layer: functorial invariants out of the quotient, for free |

## Cross-frame
`knots.md` (the first break — Gap 2 isotopy quotient + the now-unbundled ambient-space leg);
`fundamental_group.md` (the verbatim recurrence — leg 4 homotopy quotient; the free-group case here
shown a clean defect); `two_cells.md` (Shape 3 — the colimit/`q=−1` corner + ambient-space, which this
memo splits into defect vs missing-input); `adjunction.md`/`category_theory.md` (the `q=+1`-only built
corner; the free/colimit corner is this frontier); `wall_synthesis.md` (the modulus-as-data precedent
this assessment mirrors).
