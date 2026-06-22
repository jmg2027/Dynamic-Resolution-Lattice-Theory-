# Decomposition: linear logic (⊗/⅋ multiplicatives, &/⊕ additives, !/? exponentials, linear negation A^⊥, De Morgan duality, sequent calculus without weakening/contraction, proof nets, the linear λ-calculus / resource-sensitivity)

*A FRESH decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`). The
proof-theory neighbour of `curry_howard.md` (⟨proof|prop⟩, normalization = `view=fold`) and
`cut_elimination.md` (cut = composition, cut-elim = the fold-to-normal-form), but its NEW datum is
**not** about cut. Linear logic is the field that makes the **multiplicative / additive distinction the
PRIMARY logical structure** — and that distinction IS the calculus's `×↦·` / `×↦+` **character-mode
split** (SYNTHESIS Invariant A), named as two connective families. Its **involutive linear negation**
`A^⊥⊥ = A` IS the **`q = ±1` involution** (`multiplier_unimodular`; `FoldKlein.bothSwap_involutive`),
and **De Morgan duality** `(A⊗B)^⊥ = A^⊥⅋B^⊥` IS the involution swapping the two character modes
(`·↔+`, the additive-fold/multiplicative-fold exchange of `FoldKlein`). Honest verdict: **EXTEND +
PREDICTION** — the two invariants absorb linear logic with no new primitive; the named
`LinearLogic`/`⊗`/`⅋`/`!`/`Sequent`/`proofNet` objects are **predicted-not-built** (grep-confirmed
absent).*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — distinguishing, iterated: a **linear proof is a `Raw`-tree** (the same `C` as
  `curry_howard.md` / `cut_elimination.md`), but read with the calculus's structural-resource discipline
  made visible. The combine node `Raw.slash x y h` carries `h : x ≠ y` (`Fold.lean:37`, `:40`): every
  combine joins two **distinct** sub-constructions, and the fold consumes each branch **exactly once**
  (`Raw.fold_slash`: the value at `slash x y` is `c (fold x) (fold y)` — each operand used once, none
  duplicated, none discarded). That no-duplication-no-discard combine *is* linear logic's "every
  hypothesis is used exactly once": the structural rules **weakening** (discard an input) and
  **contraction** (copy an input) are exactly what the `Raw` combine does **not** offer. So
  resource-sensitivity is not an extra rule the calculus imports — it is the bare shape of the
  distinguishing combine.

- **Reading `L`** — the **character-mode reading run as the two connective families** (the load-bearing
  re-seeing, the new content vs the two neighbours):
  - **the multiplicative connectives ⊗ / ⅋ = the `×↦·` character mode.** A multiplicative connective is
    the one that *multiplies* the resource: `A⊗B` needs both A's resources and B's, the contexts
    **concatenate** (`Γ,Δ`), and the readout law is multiplicative — exactly the `×↦·` arrow
    (`det2_mul`, `legendre_mul`: a construction-preserving reading carrying combine to a multiplicative
    readout). ⅋ is its De Morgan dual.
  - **the additive connectives & / ⊕ = the `×↦+` character mode.** An additive connective *chooses* /
    *sums*: `A&B` shares one context (`Γ ⊢ A` and `Γ ⊢ B` over the **same** Γ — the context is added
    into one slot, not concatenated), `A⊕B` is a tagged sum. This is the `×↦+` arrow (`vp_mul`,
    `vp_separation`: the additive / valuation readout where combine goes to `+`). ⊕ is the dual of &.
  - **linear negation `A^⊥` (with `A^⊥⊥ = A`) = the `q = ±1` involution.** Negation is a single
    involutive self-map: applied twice it is the identity (`A^⊥⊥ = A`). That is exactly
    `multiplier_unimodular` (`q·q = 1`, `ResidueTag.lean:86`) and the involutive fold
    `bothSwap_involutive` (`FoldKlein.lean:50`). One application flips the `±1` bit; two restore it.
  - **De Morgan duality `(A⊗B)^⊥ = A^⊥⅋B^⊥` = the involution swapping the two character modes.** Linear
    negation does not merely flip a sign — it exchanges ⊗↔⅋ and &↔⊕, i.e. it swaps the multiplicative
    family with its dual and the additive family with its dual. In the fixture this is precisely
    `bothSwap = negQ ∘ recQ` (`FoldKlein.bothSwap_eq_negQ_recQ`, `:40`): the composite of the **additive
    fold** `negQ` (negation, fixes the hole pair `{0,∞}`, `FoldDuality.lean:35`) and the
    **multiplicative fold** `recQ` (reciprocal, fixes the unit pair `{±1}`, `:42`) is the fixed-point-free
    antipode that swaps **both** orbits at once. De Morgan duality is the `·↔+` mode-swap made an
    involution — the same exp/log toggle `exponential.md` reads as bidirectional character-mode.

- **Residue** — the negation reading's `q = ±1` involution surplus, and the structural-rule residue:
  - **`q = ±1` (the involution itself) — LINEAR NEGATION.** `A^⊥⊥ = A` is the involutive pole-pair: the
    tag is `±1`, two applications close (`multiplier_unimodular`; `bothSwap_involutive`,
    `klein_four_group`). The two character families sit one at each "fixed orbit" of the involution
    (additive fold fixes `{0,∞}`, multiplicative fold fixes `{±1}`, `klein_fixed_orbit_profile`,
    `:81`); negation's antipode swaps both — De Morgan.
  - **the structural-rule residue — the exponentials `!` / `?`.** `!A` re-enables weakening and
    contraction (copy / discard) on `A`: it marks "may duplicate." This is the **bridge from the
    resource-linear world back to the cartesian** — the residue the linear combine leaves un-pointed.
    The `Raw` combine is `x ≠ y` (no copy), so duplication is exactly the structural residue a linear
    reading forces but cannot host; `!` is its controlled re-admission, the `×↦·`/`×↦+` world re-entering
    the free-copy (cartesian) world. **This residue is the located absent object** — there is no `!`
    modality / `OfCourse` / contraction-rule construct in the repo (grep-confirmed).

## Re-seeing — ⟨C | L⟩

```
   a linear proof π            =  a Raw-tree; combine = slash x y (h : x ≠ y), each branch used ONCE   (C)
   resource-sensitivity        =  the Raw combine consumes each input exactly once (Raw.fold_slash);
   (no free weakening/contraction)  weakening=discard / contraction=copy are NOT offered by slash (h : x≠y)
   ⊗ / ⅋ (multiplicatives)     =  the ×↦· character mode  (det2_mul, legendre_mul; contexts concatenate Γ,Δ)
   & / ⊕ (additives)           =  the ×↦+ character mode  (vp_mul, vp_separation; one shared context Γ)
   linear negation A^⊥         =  the q=±1 involution      (multiplier_unimodular: q·q=1;
   (with A^⊥⊥ = A)                bothSwap_involutive; one application flips ±1, two restore)
   De Morgan (A⊗B)^⊥=A^⊥⅋B^⊥   =  the involution swapping the two character modes (·↔+)
                                  = bothSwap = negQ∘recQ  (additive fold ∘ multiplicative fold, FoldKlein)
   the exponentials ! / ?      =  the STRUCTURAL-RULE RESIDUE: ! marks "may duplicate" = the bridge
                                  back to the cartesian (copy/discard re-admitted; the residue the
                                  linear combine x≠y leaves un-pointed)
   cut-elimination             =  the fold to the cut-free normal form  (raw_initial / view=fold;
                                  cut_elimination.md — NOT re-derived here, cited as the neighbour)
   the linear λ-calculus       =  Curry–Howard on the linear C  (curry_howard.md's ⟨proof|prop⟩ with
   (Curry–Howard)                the no-duplication combine; proof = term = Raw)
```

So linear logic = (multiplicative ⊗ = `×↦·` / additive ⊕ = `×↦+`) + (negation `A^⊥⊥=A` = the `q=±1`
involution, De Morgan = the `·↔+` mode-swap) + (cut-elim = the fold-to-normal-form, `cut_elimination.md`)
+ (`!` = the structural-rule residue / bridge to the cartesian). No new primitive: it is the
character-mode split + the `q=±1` involution **made into a logic**, with the resource discipline that is
already the shape of the `Raw` combine.

## THE REVELATION — the multiplicative/additive split IS the `×↦·`/`×↦+` character split made the primary logical structure; linear negation IS the q=±1 involution, De Morgan IS the `·↔+` mode-swap

**COLLAPSE 1 — linear logic's two connective families ARE the calculus's two character modes.** The
calculus's deepest single arrow is the character `×↦·` / `×↦+` (SYNTHESIS Invariant A: proven the *same*
arrow across parity, valuation, det, entropy, Noether, Fourier, rep-theory — seven fields). Linear logic
is the field that takes *exactly this split* and makes it the **primary logical structure**: it splits
conjunction into a multiplicative ⊗ (contexts concatenate — resources multiply) and an additive & (one
shared context — resources add/choose), and disjunction into ⅋ and ⊕. The multiplicative law is the
`×↦·` readout (`det2_mul`, `legendre_mul`); the additive law is the `×↦+` readout (`vp_mul`,
`vp_separation`). **This is the new sentence** vs `curry_howard.md` (which read `⟨proof|prop⟩`) and
`cut_elimination.md` (which read cut = composition): linear logic does not give a new proof-object — it
gives the field where the *multiplicative/additive character distinction the calculus already runs* is
elevated to the names of the connectives. ⊗ vs & is `×↦·` vs `×↦+`, the same arrow Invariant A tracks,
now a logical primitive.

**COLLAPSE 2 — linear negation `A^⊥⊥ = A` IS the `q = ±1` involution.** Linear negation is the involutive
duality: `A^⊥⊥ = A`. The calculus has exactly one involution at the heart of its residue: the `q = ±1`
multiplier with `multiplier_unimodular` (`q·q = 1`, `ResidueTag.lean:86`), realized as the involutive
fold `bothSwap_involutive` (`FoldKlein.lean:50`, `bothSwap (bothSwap x) = x`). One application of negation
flips the `±1` bit (the dual); the second restores it — `A^⊥⊥ = A` is `q·q = 1`. The Klein four-group
`{id, negQ, recQ, bothSwap}` (`klein_four_group`, `:65`) is the full involution group: negation is an
order-2 element, and the duality is the involution, term for term.

**COLLAPSE 3 — De Morgan duality `(A⊗B)^⊥ = A^⊥⅋B^⊥` IS the involution swapping the two character modes
(`·↔+`).** This is the load-bearing find. Linear negation does not just flip a polarity; it **exchanges
the multiplicative family with its dual** (⊗↔⅋) and the additive with its dual (&↔⊕). In the calculus
the involution that swaps the additive mode and the multiplicative mode is *built*: `bothSwap = negQ ∘
recQ` (`bothSwap_eq_negQ_recQ`, `FoldKlein.lean:40`) — the **additive fold** `negQ` (negation,
`FoldDuality.lean:35`) composed with the **multiplicative fold** `recQ` (reciprocal, `:42`). `negQ` fixes
the hole orbit `{0,∞}` and swaps the units; `recQ` fixes the units and swaps the holes
(`klein_fixed_orbit_profile`, `FoldKlein.lean:81`); their composite swaps **both** and is
fixed-point-free (`bothSwap_no_fixed`, `:58`). De Morgan's `·↔+` exchange under `(–)^⊥` is exactly this
additive-fold/multiplicative-fold antipode — the same `exp/log` mode-toggle `exponential.md` reads as the
bidirectional character-mode, here run as the De Morgan involution. **NEW vs both neighbours:** neither
`curry_howard.md` nor `cut_elimination.md` touches the multiplicative/additive split or the De Morgan
involution; this is the character arrow + the `q=±1` involution read on linear logic's connectives.

**FORCING — resource-sensitivity is forced by the shape of the `Raw` combine, not stipulated.** Linear
logic forbids free weakening and contraction; the calculus's combine `Raw.slash x y h` has `h : x ≠ y`
(`Fold.lean:40`) and the fold uses each branch exactly once (`Raw.fold_slash`, `:37`). So "every
distinction is used exactly once" is the bare distinguishing combine: copy (contraction) would need a
branch equal to itself (`x = x`, blocked by `h`), and discard (weakening) would need the fold to drop a
branch (it does not — `fold_slash` mentions both). Resource-linearity is *forced* by the combine, and the
**cartesian** logic (free copy/discard) is the residue re-admitted by `!`.

**SPINE — the exponentials `!`/`?` are the structural-rule residue (the bridge to the cartesian).** `!A`
re-enables contraction and weakening on `A` — it marks "this resource may be duplicated/discarded." This
is the residue the linear combine leaves un-pointed: the `×↦·`/`×↦+` linear world is the resource-exact
corner, and `!` is the controlled gate back to the free-copy cartesian world. It is the structural-rule
analogue of how `derivative.md`'s dropped `O(h²)` residue is *revived* as the Itô correction (SYNTHESIS
`scaling`): a residue the primary reading forces but cannot host, named and re-admitted one modality up.
The `!`/`?` modality is the **located absent object** — no contraction/copy construct exists in the repo.

## VALIDATE — verdict

**EXTEND + PREDICTION, no new primitive.** Model v7.1 absorbs linear logic with zero new axes:
- multiplicative ⊗/⅋ vs additive &/⊕ = the **character-mode split** `×↦·` / `×↦+` (Invariant A), made
  the primary logical structure — `det2_mul`/`legendre_mul` vs `vp_mul`/`vp_separation`;
- linear negation `A^⊥⊥ = A` = the **`q = ±1` involution** (`multiplier_unimodular`,
  `bothSwap_involutive`);
- De Morgan `(A⊗B)^⊥ = A^⊥⅋B^⊥` = the involution **swapping the two character modes** (`bothSwap = negQ
  ∘ recQ`, the additive-fold/multiplicative-fold antipode);
- resource-sensitivity = the `Raw` combine's no-duplication-no-discard (`Raw.slash`'s `x ≠ y`,
  `Raw.fold_slash` each branch once);
- cut-elimination = the fold-to-normal-form (`cut_elimination.md`, cited not re-derived);
- the linear λ-calculus = Curry–Howard on the linear `C` (`curry_howard.md`, cited);
- `!`/`?` = the **structural-rule residue** / bridge back to the cartesian.

It is the calculus's two load-bearing invariants — the character arrow and the `q=±1` involution — read
on the one logic that takes *both* as its primitives. The verdict is EXTEND (the invariants absorb it) +
PREDICTION (the named field objects are absent).

**Does linear logic need a genuine primitive that is absent? — HONEST: the named objects, yes.** The
*engines* are fully built and PURE (the two character laws, the `q=±1` involution, the Klein involution
group, the no-duplication combine, the fold-to-normal-form). What is **absent** (grep-confirmed, very
likely as the prompt predicted) is every **named** linear-logic object: no `LinearLogic`, no `⊗`/`⅋`/`&`/
`⊕` connective inductive, no `LinearNeg`/`A^⊥` with a built De Morgan theorem on a formula type, no `!`/`?`
modality / `OfCourse` / promotion-dereliction rules, no `Sequent` with the structural rules
*removed*, no `proofNet`/correctness-criterion object. The grep for `linear_logic|LinearLogic|proofNet|
proof_net|Sequent|par|tensor⊗⅋` returned only `TensorCalculus.lean` (the differential-geometry tensor — a
**false friend**, not the linear ⊗) and the `cut_elimination.md` toy `CutElimination.lean`. The
"⊗=`×↦·` / &=`×↦+` / `A^⊥⊥=A`=`q=±1` / De Morgan=`bothSwap`" identification is the decomposition's framing
on the existing character + involution + combine engine, not a built linear sequent calculus. This is the
exact dual of `curry_howard.md`'s absent typed λ-calculus and `cut_elimination.md`'s absent `Sequent`/
`Formula` Hauptsatz.

## Verified Lean anchors (file:line:theorem — all grep/Read-confirmed this session; purity via `tools/scan_axioms.py` from repo root)

| Leg | Theorem / def (file:line : name) | Status |
|---|---|---|
| **linear proof = `Raw`-tree; combine = `slash x y (h : x ≠ y)`** | `Lens/LensCore.lean` `Raw`; `Theory/Raw/Fold.lean:22 Raw.fold` (catamorphism); `:30 Raw.fold_a`/`:33 Raw.fold_b` | (def) ✓ |
| **★ resource-sensitivity = no-duplication-no-discard combine** (each branch used ONCE; copy needs `x=x`, blocked by `h:x≠y`) | `Theory/Raw/Fold.lean:37 Raw.fold_slash` (value at `slash x y` = `c (fold x) (fold y)`, each operand once) | PURE (folds used PURE) ✓ |
| **★ multiplicatives ⊗/⅋ = the `×↦·` character mode** | `…/Real213/Markov/SternBrocotMarkov.lean:104 det2_mul`; `…/ModArith/LegendreMultiplicative.lean:77 legendre_mul` | ∅-axiom PURE ✓ (130/0; 5/0) |
| **★ additives &/⊕ = the `×↦+` character mode** | `Meta/Nat/VpMul.lean:165 vp_mul`; `Meta/Nat/VpSeparation.lean:172 vp_separation` | ∅-axiom PURE ✓ (10/0) |
| **★ linear negation `A^⊥⊥ = A` = the `q = ±1` involution** | `Lib/Math/Foundations/ResidueTag.lean:86 multiplier_unimodular` (`q·q=1`); `:90 tag_inj_multiplier` | ∅-axiom PURE ✓ (55/0) |
| **involution realized as a fold; `A^⊥⊥=A` = `bothSwap∘bothSwap=id`** | `Lens/Number/FoldKlein.lean:50 bothSwap_involutive`; `Lens/Number/FoldDuality.lean:50 negQ_involutive`, `:52 recQ_involutive` | ∅-axiom PURE ✓ (9/0; 13/0) |
| **★ De Morgan `(A⊗B)^⊥=A^⊥⅋B^⊥` = the involution swapping the two character modes (`·↔+`)** | `Lens/Number/FoldKlein.lean:40 bothSwap_eq_negQ_recQ` (`negQ∘recQ = bothSwap`, additive fold ∘ multiplicative fold); `:43 bothSwap_eq_recQ_negQ` (commute) | ∅-axiom PURE ✓ |
| the two character families = the two fixed-orbit folds (additive fixes `{0,∞}`, multiplicative fixes `{±1}`) | `Lens/Number/FoldKlein.lean:81 klein_fixed_orbit_profile`; `:65 klein_four_group`; `:58 bothSwap_no_fixed` (De Morgan antipode fixed-point-free) | ∅-axiom PURE ✓ |
| the `q=±1` involution as the residue tag's two poles | `Lib/Math/Foundations/ResidueTag.lean:228 residue_tag_two_poles`; `:180 golden_is_converge` | ∅-axiom PURE ✓ |
| **cut-elimination = the fold-to-normal-form** (cited from `cut_elimination.md`, NOT re-derived) | `Lens/Foundations/SemanticAtom.lean:412 raw_initial`; `Lens/Foundations/UniversalDistinguishing.lean:103 dhom_unique_pointwise` | ∅-axiom PURE ✓ |
| **the linear λ-calculus = Curry–Howard on the linear `C`** (cited from `curry_howard.md`) | `Theory/Raw/Lambek.lean:273 no_infinite_descent` (strong normalization, `q=+1` floor) | ∅-axiom PURE ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py` from repo root):**
- `E213.Lens.Number.FoldKlein` → **9 pure / 0 dirty** (`bothSwap_involutive`, `bothSwap_eq_negQ_recQ`, `klein_four_group`, `klein_fixed_orbit_profile`, `bothSwap_no_fixed`)
- `E213.Lens.Number.FoldDuality` → **13 pure / 0 dirty** (`negQ_involutive`, `recQ_involutive`)
- `E213.Lib.Math.Foundations.ResidueTag` → **55 pure / 0 dirty** (`multiplier_unimodular`, `tag_inj_multiplier`, `residue_tag_two_poles`, `golden_is_converge`)
- `E213.Lib.Math.NumberSystems.Real213.Markov.SternBrocotMarkov` → **130 pure / 0 dirty** (`det2_mul` PURE)
- `E213.Meta.Nat.VpMul` → **10 pure / 0 dirty** (`vp_mul` PURE)
- `E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative` → **5 pure / 0 dirty** (`legendre_mul` PURE)

## Dropped / flagged (honest)

- **A genuine `LinearLogic` / `⊗`/`⅋`/`&`/`⊕` connective calculus — ABSENT (predicted-not-built).** No
  `Formula` inductive with the multiplicative/additive connectives, no `Sequent` with the structural
  rules removed, no two-sided/one-sided linear sequent calculus. Grep
  (`linear_logic|LinearLogic|proofNet|proof_net|Sequent|par|tensor`) returned only `TensorCalculus.lean`
  (the differential-geometry **tensor**, a false friend) and the `cut_elimination.md` toy. The
  "⊗=`×↦·` / &=`×↦+`" identification is the decomposition's framing on the existing character laws.
- **Linear negation `A^⊥` + a De Morgan theorem ON A FORMULA TYPE — ABSENT.** The involution
  (`multiplier_unimodular`, `bothSwap_involutive`) and the mode-swap (`bothSwap = negQ∘recQ`) are
  PURE-built on the `±1` tag and the `Q4` fixture; the *named* `A^⊥` on a linear formula with
  `(A⊗B)^⊥ = A^⊥⅋B^⊥` proved by formula induction is the open instance.
- **The `!`/`?` exponentials / promotion-dereliction / contraction-weakening rules — ABSENT.** No `!`
  modality, no `OfCourse`, no controlled-copy construct. This is the **structural-rule residue** named in
  the Spine: the bridge from the resource-linear corner back to the cartesian, the residue the
  no-duplication combine (`Raw.slash`'s `x ≠ y`) leaves un-pointed. Located, not built.
- **Proof nets / the correctness criterion — ABSENT.** No `proofNet`/Danos–Regnier object; grep-empty.
  The geometric-of-interaction / correctness-criterion side has no `Raw`/`Lens` term yet.
- **"⊗=`×↦·` ∧ &=`×↦+` ∧ `A^⊥⊥=A`=`q=±1` ∧ De Morgan=`bothSwap`" as ONE welded theorem — conceptual.**
  Lean certifies each leg separately (the two character laws, `multiplier_unimodular`/`bothSwap_involutive`,
  `bothSwap_eq_negQ_recQ`); the single theorem welding them into "linear logic = the character split + the
  involution made a logic" is the decomposition's framing on verified PURE objects.
- **Buildable witness (verified shape, NOT built this session):** a `LinearFormula` inductive with
  `tensor`/`par`/`with`/`plus`/`neg` constructors + a `dual : LinearFormula → LinearFormula` with a
  `dual_dual : dual (dual A) = A` lemma (the `multiplier_unimodular` / `bothSwap_involutive` shape lifted
  to formulas) and a `dual_tensor : dual (tensor A B) = par (dual A) (dual B)` De Morgan lemma (the
  `bothSwap_eq_negQ_recQ` shape on the connective swap). `dual_dual` is a routine `cases`/`rfl` involution
  (the exact shape of `bothSwap_involutive`'s `intro x; cases x <;> rfl`); the De Morgan lemma is `rfl`
  on the right constructor pairing. This is the linear-logic analogue of how `FreeReduction.lean` cashed
  the colimit Side-A and the toy `CutElimination.lean` cashed cut. Flagged as the named promotion target;
  no proposed numeric/decide witness is asserted (none is needed — the legs are involutions, not
  inequalities).

## Cross-frame

`curry_howard.md` (⟨proof|prop⟩, the linear λ-calculus = Curry–Howard on the no-duplication `C`,
normalization = `view=fold`, SN = `no_infinite_descent`); `cut_elimination.md` (cut = the 2-category's
composition, cut-elimination = the fold-to-normal-form, the subformula property = the fold's no-new-atoms
law — linear logic's cut-elim is cited from there, NOT re-derived); `exponential.md` (the bidirectional
`×↦·`/`×↦+` character-mode toggle = the exp/log direction the De Morgan involution swaps);
`hopf_algebras.md` (the ⊗/co-⊗ duality = the additive/multiplicative fold duality, comultiplication
native); `convex_duality.md` (`f**=clo` involutive duality — the `q=+1` closure pole, the convergent
companion to negation's `±1` involution); SYNTHESIS Invariant A (the `×↦·`/`×↦+` character arrow that
linear logic elevates to two connective families) + Invariant B (the `q=±1` residue tag whose involution
IS linear negation). **VERDICT: EXTEND + PREDICTION** — linear logic = the calculus's two invariants made
into a logic: the multiplicative/additive split = the `×↦·`/`×↦+` character-mode split made primary
(`det2_mul`/`legendre_mul` vs `vp_mul`/`vp_separation`), linear negation `A^⊥⊥=A` = the `q=±1` involution
(`multiplier_unimodular`, `bothSwap_involutive`), De Morgan = the `·↔+` mode-swap (`bothSwap = negQ∘recQ`),
resource-sensitivity = the no-duplication combine (`Raw.slash`'s `x≠y`, `Raw.fold_slash`), cut-elim = the
fold-to-normal-form (cited), `!`/`?` = the structural-rule residue / bridge to the cartesian. No new
primitive. The single precise absence: a *named* `LinearLogic`/`⊗`/`⅋`/`!`/`Sequent`/`proofNet` object —
predicted-not-built, grep-confirmed (the one `tensor` hit is the differential-geometry false friend).
