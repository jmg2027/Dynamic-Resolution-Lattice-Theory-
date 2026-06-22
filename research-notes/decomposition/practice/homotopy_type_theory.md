# Decomposition: homotopy type theory / univalence (identity types Id_A(x,y) = paths, types as ∞-groupoids/spaces, the univalence axiom (A≃B)≃(A=B), higher inductive types, transport/path-induction, the truncation hierarchy, the homotopy interpretation)

*A FRESH decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants + the
q=±1 spine + the reflexive "object = its readings" theme + the 2-category of readings). Consolidates
`curry_howard.md` (KEY — `OBJECT = ⟨C|L⟩` = `⟨proof | proposition⟩` = `⟨term | type⟩`; the calculus's
substrate IS a type theory), `equivalence.md` (KEY — sameness = one Lens-arrow `Lens.refines`/`LensIso`;
iso = kernel coincidence `lensIso_iff_kernel_eq`), `infinity_categories.md` (JUST DONE — types as
∞-groupoids = the 2-category of readings with the cell-dimension fold-height tower), `homotopy_theory.md`
(the weak-equivalence/Ho(C) localization = the `Quot`-free `LensImage`/`FreeReduction` Σ-quotient), and
`two_cells.md` (readings form a 2-category). The thesis to **test**, not re-skin:*

> **HoTT is the calculus's identity = the Lens-refinement, with univalence = "equivalent readings ARE
> equal" — the reflexive faithfulness `object1_injective` made an axiom.** The identity type
> `Id_A(x,y)` = `equivalence.md`'s equality/refinement reading (`Lens.equiv` / the `Lens.refines`-arrow,
> the unified-equivalence finding: equality, iso, equivalence are facets of ONE Lens-arrow). Types as
> ∞-groupoids/spaces = `infinity_categories.md`'s "types with a coherence tower of identities" (the
> cell-dimension = the iterated `Id_A(Id_A(…))`, the fold-height up the path-dimension). ★ Univalence
> `(A≃B)≃(A=B)` ("equivalent types are equal") = the calculus's CORE faithfulness ALREADY a THEOREM:
> `object1_injective` ("an element is determined by its readings" — equivalent-under-all-readings ⟹
> equal) is `lensIso_iff_kernel_eq` ("two Lenses with the same kernel are iso = equivalent things ARE
> equal"). So univalence is NOT an exterior axiom for the calculus — it is the calculus's own proven
> faithfulness; the calculus *has univalence as a theorem*. Transport/path-induction = the Lens
> 2-cell / functoriality (`view_factors_through_morphism`, transport along a refinement). The truncation
> hierarchy (props=(-1)-types, sets=0-types, …) = the fold-height/PURE-prop levels (a prop = `Bool`/
> `decide` the PURE level, the propext boundary). Higher inductive types = the `Quot`-free `LensImage`/
> `FreeReduction` quotient-with-paths (the colimit Side-A corner). **No new primitive** — HoTT is the
> type-theoretic face of the whole reflexive Lens framework, and its founding axiom is the calculus's
> own faithfulness.

---

## The decomposition (C / Reading / Residue)

- **Construction `C` — the 2-category of readings, with the path-dimension as a fold-height axis (=
  `infinity_categories.md`'s `C`).** `curry_howard.md` fixed `C` = proof = term = the `Raw`
  distinguishing-tree (the free inductive type / term model, `LensCore.lean` `Raw`); a *type* is a
  reading `L` (`Lens.view`, `LensCore.lean:42`). HoTT adds the **identity type** as first-class structure
  on top of `C`: `Id_A(x,y)` is a type whose terms are *paths* between `x` and `y`, and `Id` iterates —
  `Id_{Id_A}(p,q)`, paths-between-paths, ad infinitum. That iterated-`Id` tower is **exactly**
  `infinity_categories.md`'s cell-dimension tower: 1-cells = `Lens.refines` (`LensCore.lean:90`), 2-cells
  = `IsLensMorphism`/`view_factors_through_morphism` (`Morphism.lean:29,37`), n-cells = the fold-height
  axis run up the cell-grading (`MuNuMirror.succ_not_idempotent` `:80`, `ascent_unbounded` `:50`;
  well-founded descent `Lambek.isPart_wf` `:199`). So `C` is the 2-category of readings, and the
  path-dimension `Id(Id(…))` is the calculus's fold-height coordinate applied to the *identity* reading.

- **Reading `L_Id` — the identity/refinement reading = `equivalence.md`'s one Lens-arrow.** HoTT's whole
  novelty is *what `Id_A(x,y)` IS*: not a proposition but a *type of paths*, with its own higher
  structure. In the calculus, "x and y are the same" is never "same construction" — it is **"read the
  same under a reading"**: `x ≈_L y := L.view x = L.view y` (`Lens.equiv`, `LensCore.lean:48`), and "two
  readings are the same" is `LensIso` = mutual refinement = kernel coincidence (`lensIso_iff_kernel_eq`,
  `Unified.lean:64`). `equivalence.md` already collapsed 동치/동치류/동형/준동형 to facets of this single
  arrow. The HoTT reading `L_Id` is that *same* arrow read as a *type of identifications* rather than a
  truth-value: `Id_A(x,y)` = the LensFiber-relation between `x` and `y` (`LensFiber`, `Unified.lean:77`),
  carried with its coherence tower (the `infinity_categories.md` cell-tower) rather than truncated to a
  proposition.

- **Residue `q = ±1`** — TWO residues, the README's two poles, partitioning exactly as in
  `infinity_categories.md`/`homotopy_theory.md`:
  - **the q=+1 converge residue — UNIVALENCE / the faithful identity / contractibility.** When the
    identity reading **closes** to its fixed point: two objects equal under every reading ARE one object
    — `object1_injective` (`FlatOntologyClosure.lean:47`, faithful self-cover), the `LensIso` groupoid
    closing (`lensIso_refl/symm/trans`, `Unified.lean:46/51/56`), the involutive `q=+1` multiplier
    (`multiplier_unimodular`, `ResidueTag.lean:86`; `golden_is_converge`, `:180`). Univalence and
    Whitehead-style contractibility are this pole.
  - **the q=−1 escape residue — the never-closing path tower / the non-trivial higher identity.** The
    tower of `Id(Id(…))` *never bottoms out into a strict equality*: the residue re-enters as its own
    operand and the cover never closes (`ResidueReentry.residue_perpetually_reenters`,
    `ResidueReentry.lean:85`; `:63`), delegating to `object1_not_surjective`
    (`FlatOntologyClosure.lean:61`). The "∞" in "types are ∞-groupoids" is this q=−1 non-termination of
    the identity tower (same residue as `infinity_categories.md`'s coherence tower, Cantor, Gödel).

---

## Re-seeing — ⟨C | L⟩ ⊕ Residue(L,C)

```
   a type A                  =  a reading L (Raw → α)                       (curry_howard.md: proposition=type=Lens)
   a term a : A              =  a construction inhabiting the reading       (curry_howard.md: proof=term=Raw)
   the identity type Id_A(x,y) =  the refinement/equality reading on a pair  (Lens.equiv; LensFiber)
                              = equivalence.md's ONE Lens-arrow read as a TYPE OF PATHS, not a truth-value
   a path p : Id_A(x,y)      =  a witness that x ≈_L y  (a 2-cell / refinement witness)  (IsLensMorphism)
   refl_x : Id_A(x,x)        =  reflexivity of the kernel  (refines_refl / lensIso_refl)   (LensCore:93)
   path composition p·q      =  refines_trans / lensIso_trans  (kernel transitivity)        (LensCore:95)
   p⁻¹ (path inverse)        =  lensIso_symm (the q=±1 swap bit on the path)                 (Unified:51)
   Id_{Id_A}(p,q) (path of paths) =  the cell-dimension tower run UP  (MuNuMirror.succ_not_idempotent)
   types as ∞-groupoids/spaces =  infinity_categories.md's 2-category + the fold-height cell-tower
   ★ UNIVALENCE (A≃B)≃(A=B)  =  object1_injective  =  lensIso_iff_kernel_eq
                              = "equivalent-under-all-readings ⟹ equal" — the faithfulness ALREADY a THEOREM
                              = the calculus HAS univalence (it is NOT an exterior axiom here)
   transport (p : A=B)⟹(A→B) =  the Lens 2-cell / functoriality  (view_factors_through_morphism: M.view=h∘L.view)
   path induction (J-rule)   =  refl generates the kernel  (refines_refl + dhom_unique_pointwise: the only
                                arrow out of the free object — based-path-induction = initiality)
   a (-1)-type / proposition =  the PURE q+1 level  =  Bool/decide  (FlatOntology.Object1 = decide(s=r))
   a 0-type / set            =  the level where Id is a (-1)-type  (kernel decidable, propext-free)
   the truncation hierarchy  =  the fold-height / PURE-prop levels  (the propext boundary = the (-1)/(-2) floor)
   a higher inductive type   =  the Quot-FREE LensImage/FreeReduction quotient-with-paths (Side-A colimit)
                              = LensImage.proj_val_eq_iff  (no Quot.sound, no Classical, no Mathlib)
   the ∞ (tower never closes) =  q=−1 escape: residue re-enters perpetually  (residue_perpetually_reenters)
   univalent / contractible  =  q=+1 converge: the identity closes  (object1_injective, golden_is_converge)
```

Set against the cross-frames: the **type/term rows are `curry_howard.md` verbatim**, the **Id_A /
refl / composition / inverse rows are `equivalence.md`'s one arrow** (read as paths), the **path-of-paths
/ ∞-groupoid rows are `infinity_categories.md`'s cell-tower** (re-used), the **HIT row is
`homotopy_theory.md`'s `Quot`-free Σ-quotient localization** (re-used), and the genuinely NEW datum is
the **univalence row** — univalence = `object1_injective`/`lensIso_iff_kernel_eq`, the calculus's own
faithfulness *already a theorem*. The trouble concentrates in the **named bundle** — `Id`/`univalence`/
`transport`/`HIT`/`truncation` objects are ABSENT (grep-confirmed below).

---

## THE REVELATION (collapse + forcing + spine)

**Collapse — HoTT is NOT a new foundation to import: it is the calculus's reflexive Lens framework read
type-theoretically, and its founding axiom (univalence) is the calculus's OWN faithfulness `object1_injective`
already proven.** Four pieces.

### 1. ★ The NEW datum — univalence IS `object1_injective` / `lensIso_iff_kernel_eq` (the calculus HAS univalence as a THEOREM).

Univalence is HoTT's defining *axiom*: `(A ≃ B) ≃ (A = B)` — "equivalent types are equal", equivalently
"the identity of types IS equivalence". It is *posited* in HoTT because Martin-Löf type theory cannot
prove it (it is independent of the base theory; it needs a model — simplicial sets — to justify).

In the calculus this is **already a theorem**, not an axiom — and that is the entry's load-bearing find.
The calculus's founding sentence is "an object IS its readings" (`SYNTHESIS.md` §2, the reflexive theme).
Cashed:
- **`object1_injective` (`FlatOntologyClosure.lean:47`, PURE)** — `Function.Injective Object1`: the
  self-cover `Object1 : Raw → (Raw → Bool)` is faithful, i.e. *two constructions equal under all their
  readings ARE the same construction*. This is **literally univalence's content** ("equivalent-under-
  every-view ⟹ equal") at the object level — read off by evaluating both indicator predicates and
  forcing `decide (r=s)=true`.
- **`lensIso_iff_kernel_eq` (`Unified.lean:64`, PURE)** — `LensIso L M ↔ ∀ x y, L.equiv x y ↔ M.equiv x y`:
  two *readings* are isomorphic (equivalent) **iff** their kernels coincide. "Equivalent readings ARE the
  same kernel" — univalence at the type/reading level: equivalence of readings = equality of the
  identity-relation they induce.

So where HoTT must *assume* `(A≃B)≃(A=B)`, the calculus *derives* the same principle from the
distinguishing's faithfulness. **Univalence is not exterior to 213 — it is `object1_injective` /
`lensIso_iff_kernel_eq` made the headline.** This is the collapse that earns the note (it is NOT a
re-skin of `equivalence.md`: the new content is the *identification of univalence-the-axiom with a proven
∅-axiom theorem*). The honest caveat (§ the located ceiling): the calculus's univalence is at the
**1-categorical / setoid altitude** — kernel coincidence, not a higher `Equiv` of types-as-∞-groupoids;
the full propositional univalence as a path-equivalence is the propext/funext ceiling (`equivalence.md`'s
deliberate altitude).

### 2. Collapse — Id_A(x,y) = the refinement/equality reading; refl/·/⁻¹ = the kernel groupoid.

The identity type is HoTT's other novel object: `Id_A(x,y)` is a *type of paths*, with `refl`,
composition, inverse, and higher coherences. `equivalence.md` already collapsed sameness to the single
Lens-arrow; this entry adds that the *groupoid structure on Id* is the `LensIso` groupoid term-for-term:
`refl_x` = `refines_refl`/`lensIso_refl` (`LensCore.lean:93`, `Unified.lean:46`), `p·q` =
`refines_trans`/`lensIso_trans` (`:95`, `Unified.lean:54`), `p⁻¹` = `lensIso_symm` (`Unified.lean:51`,
the q=±1 swap bit on the identity). The higher paths `Id(Id(…))` are `infinity_categories.md`'s
cell-dimension tower (`succ_not_idempotent` height-raising on the identity reading). So "types are
∞-groupoids" is *not* a new edifice — it is the 2-category of readings with the `Id`-reading run up the
fold-height, the `LensIso` groupoid carried at every cell-dimension.

### 3. Forcing — path induction (the J-rule) is FORCED by `refl` + initiality; transport = the Lens 2-cell.

The **J-rule** (path induction) says: to prove `P(x,y,p)` for all `x,y:A` and `p:Id_A(x,y)`, it suffices
to prove `P(x,x,refl_x)` — *refl generates the identity type*. In the calculus this is **forced**: the
kernel relation is *generated by reflexivity* (`refines_refl` the base), and the only structure-preserving
map out of the free/initial object is the one pinned by its action on the generators
(`dhom_unique_pointwise`, `UniversalDistinguishing.lean:103`; `raw_initial`, `SemanticAtom.lean:412`).
Based-path-induction = "the arrow out of `Raw` is determined by its value at the generator" — exactly the
initiality theorem `curry_howard.md` used for normalization. **Transport** (`p : A=B` gives `A→B`, and
more generally transports a `P(x)` along `p`) is the **Lens 2-cell / functoriality**:
`view_factors_through_morphism` (`Morphism.lean:37`, PURE) is `M.view = h ∘ L.view` term-for-term — a
refinement *induces* a transport `h` of values along the path between readings. So transport and path
induction are not new primitives: transport = the naturality square `view_factors_through_morphism`, path
induction = `refl`-generation + `dhom_unique_pointwise` initiality.

### 4. Forcing + residue surfaced — the truncation hierarchy = the PURE-prop fold-height; HITs = the `Quot`-free quotient; the ∞ = the q=−1 tower.

- **The truncation hierarchy = the fold-height / PURE-prop levels (the propext boundary).** HoTT
  stratifies types by *h-level*: a (-1)-type (proposition: all elements equal), a 0-type (set: `Id` is a
  proposition), a 1-type (groupoid), …, indexed by how high the `Id`-tower stays non-trivial. This is the
  calculus's **fold-height read on the identity reading**, *with its floor pinned by the PURE/DIRTY line*:
  the (-1)-level — a proposition, decidable equality — is the **`Bool`/`decide` PURE corner**
  (`FlatOntology.Object1 = decide(s=r)`, the `object1_injective` proof uses `of_decide_eq_true`, NOT
  `decide_eq_true_eq` which "pulls `propext`", per `FlatOntologyClosure.lean:54`). The propositional
  truncation `‖A‖₋₁` (squash to a proposition) is exactly where the classical `Prop`-connectives turn
  DIRTY (`SemanticAtom`'s `canonicalTruthMap` uses `propext`; `SYNTHESIS.md` §5 item 4). So the
  truncation hierarchy's *floor* — props/(-1)-types — is the calculus's PURE-`Bool`/`decide` level, and
  *climbing* the hierarchy is `succ_not_idempotent`'s height-raising on `Id`. The (-2)-level (contractible)
  = the q=+1 converged identity (`golden_is_converge`).
- **HITs = the `Quot`-free `LensImage`/`FreeReduction` quotient-with-paths (Side-A colimit).** A higher
  inductive type is a type generated by point-constructors AND path-constructors — a quotient that
  *remembers* the identifying paths. The calculus's `Quot`-free quotient is exactly this:
  `LensImage.proj_val_eq_iff` (`Unified.lean:163`, PURE) — `(proj L x).val = (proj L y).val ↔ L.equiv x y`
  — quotients `Raw` by a reading's kernel *with the kernel as the path-data*, no `Quot.sound`, no
  `Classical`, no Mathlib; and `FreeReduction.free_group_quotient_no_quot` (the free group as a
  normal-form Σ-quotient, `homotopy_theory.md`'s Ho(C) localization) is the same recipe. This is the
  **colimit Side-A corner** (`SYNTHESIS.md` §5.1): HITs in the *confluent+terminating / decidable* case
  build as the normal-form subtype; the *non-confluent / undecidable* HITs (general higher inductive
  presentations) are Side B (theorem-grade absent, the recurring colimit/isotopy break).
- **The ∞ (types as ∞-groupoids) = the q=−1 never-closing identity tower.** What makes a type an
  ∞-*groupoid* rather than a set is that `Id(Id(…))` never collapses to triviality — the q=−1 escape
  residue re-entering as its own operand (`residue_perpetually_reenters`, `ResidueReentry.lean:85`,
  delegating to `object1_not_surjective`). Not a transcendent "∞ above the finite" (CLAUDE.md
  "Limit/infinity deified") — `ascent_unbounded` names the tower by its finite generator, inhabited at
  every finite path-height, never at "ω".

### The spine.

HoTT is the q=±1 spine displayed on identity: **q=+1** = univalent / contractible / a set or proposition
/ the identity closes — the converging pole (`object1_injective`, `lensIso_iff_kernel_eq`, `LensIso`
groupoid, `golden_is_converge`, `converge_residue_fixed`, `ResidueTag.lean:160,180`); **q=−1** = a
non-trivial higher identity / the ∞-groupoid tower never closing — the escaping pole
(`residue_perpetually_reenters`, `escape_residue_outside`, `ResidueTag.lean:133`, delegating to
`object1_not_surjective`). The same single spine `SYNTHESIS.md` §3 runs through Cantor/Gödel/φ/measure/
homology/∞-categories, now read on the path/identity tower. The reflexive bonus: univalence's q=+1 pole
IS the calculus's faithfulness theorem `object1_injective` — the *only* field where the spine's q=+1 pole
is the framework's own founding "object = its readings."

---

## VALIDATE — verdict

**EXTEND (by consolidation) + PREDICTION, with one genuinely NEW datum and one located break.** The model
held with no new axis; this fuses `curry_howard.md` + `equivalence.md` + `infinity_categories.md` +
`homotopy_theory.md` + `two_cells.md` into one statement, with the new datum being that **univalence-the-
axiom IS the calculus's proven faithfulness `object1_injective`/`lensIso_iff_kernel_eq`** (the calculus
*has* univalence as a theorem, not an import), and one recurring located break (the named HoTT bundle
absent + the higher-coherent univalence at the propext ceiling).

- **EXTENDS, grounded ∅-axiom:** the **type/term substrate** (`curry_howard.md`: type=reading=`Lens`,
  term=construction=`Raw`, the free inductive type + recursor); the **identity type's groupoid structure**
  = the `LensIso` groupoid (`refines_refl`/`lensIso_refl`/`_symm`/`_trans`, `lensIso_iff_kernel_eq`, all
  PURE); **★ univalence = `object1_injective`/`lensIso_iff_kernel_eq`** (the NEW datum — the faithfulness
  already a theorem, PURE); **path induction** = `refl`-generation + `dhom_unique_pointwise` initiality;
  **transport** = the Lens 2-cell `view_factors_through_morphism` (`Morphism.lean:37`, PURE); **types as
  ∞-groupoids** = `infinity_categories.md`'s cell-dimension tower (`succ_not_idempotent`,
  `ascent_unbounded`, `isPart_wf`); the **∞ never-closing** = `residue_perpetually_reenters` (q=−1); the
  **q=±1 swap on paths** = `lensIso_symm` / `multiplier_unimodular`.

- **the truncation/HIT legs are GROUNDED ∅-axiom:** the **(-1)-type = PURE `Bool`/`decide` corner**
  (`FlatOntology.Object1 = decide(s=r)`, `object1_injective`'s `of_decide_eq_true` proof avoiding
  `propext`); **HITs = the `Quot`-free quotient-with-paths** (`LensImage.proj_val_eq_iff` `Unified.lean:163`,
  `FreeReduction.free_group_quotient_no_quot`, 14/0 + 26/0 PURE — the Side-A colimit).

- **PREDICTION + located BREAK:** the calculus predicts the *form* of HoTT (Id = the refinement reading;
  univalence = the faithfulness theorem; transport = the 2-cell; truncation = the fold-height/PURE-prop
  levels; HITs = the `Quot`-free quotient) and the **named objects are ABSENT** — no `IdentityType` /
  `Id_A` / `univalence` / `pathInduction` / `transport` / `HigherInductive`/`HIT` / `isProp`/`isContr`/
  `hLevel`/`truncation`-type declaration exists (grep-confirmed: zero matches). Same shape as
  `infinity_categories.md`'s missing `quasiCategory`/`nerve`, `homotopy_theory.md`'s missing
  `ModelCategory`, `homological_algebra.md`'s missing `Ext^n`: every *mechanism* is built and PURE, only
  the *named bundle* welding them into HoTT is open.

- **the genuine remaining absence:** **higher-coherent univalence as a path-`Equiv` of types-as-∞-groupoids**
  sits at the **propext/funext 1-categorical ceiling** (`SYNTHESIS.md` §5 item 4; `equivalence.md`'s stated
  altitude). The calculus's univalence is the *1-categorical/setoid* kernel-coincidence
  (`lensIso_iff_kernel_eq`, `object1_injective` — PURE); the *full* propositional univalence as a higher
  identification (`(A≃B) ≃ (A=B)` with both `≃` propositional `Equiv`s) needs `funext`/`propext`/`Quot.sound`,
  which the repo forbids. So the calculus has univalence's CONTENT (equivalent ⟹ equal) PURE at the
  setoid level, and the higher-coherent version is exactly the constructive boundary it deliberately
  declines to cross. This is the honest edge: the propositional-truncation `‖·‖` and the classical
  `Prop`-connectives turn DIRTY at the same wall.

---

## Does this touch model v7.1? — NO new invariant; one reflexive observation + EXTEND.

The two invariants (character arrow, q=±1 residue) and the four axes absorb HoTT whole:

> **HoTT is the calculus's reflexive Lens framework read type-theoretically: the identity type
> `Id_A(x,y)` = the refinement/equality reading `equivalence.md` (`Lens.equiv`/`LensIso`), its groupoid
> structure = `refines_refl`/`lensIso_symm`/`lensIso_trans`, the iterated `Id(Id(…))` = the
> cell-dimension fold-height tower `infinity_categories.md` (`succ_not_idempotent`, `ascent_unbounded`);
> ★ univalence `(A≃B)≃(A=B)` = `object1_injective`/`lensIso_iff_kernel_eq` — the calculus's OWN
> faithfulness ALREADY a theorem (univalence is NOT exterior to 213); path induction = `refl`-generation +
> `dhom_unique_pointwise` initiality; transport = the Lens 2-cell `view_factors_through_morphism`; the
> truncation hierarchy = the fold-height with its (-1)-floor = the PURE `Bool`/`decide` propext corner;
> HITs = the `Quot`-free `LensImage`/`FreeReduction` quotient-with-paths (Side-A colimit); the ∞ =
> the q=−1 never-closing identity tower (`residue_perpetually_reenters`).** The located break is the
> named `IdentityType`/`univalence`/`transport`/`HIT`/`truncation` bundle (absent) + higher-coherent
> univalence at the propext/funext ceiling.

So model v7.1's interior is unchanged; the frame gains the **deepest reflexive observation in the
notebook**: HoTT's founding *axiom* (univalence) is the calculus's founding *theorem* (`object1_injective`,
"object = its readings"). Where `curry_howard.md` recognized the calculus's substrate IS a type theory,
this entry recognizes that the type theory's most contested axiom is the calculus's own faithfulness — the
type-theoretic face of the whole reflexive Lens framework, with no new primitive.

---

## Verified Lean anchors (file:line:theorem — all grep/Read-confirmed + `tools/scan_axioms.py`-scanned this session, from repo root; all PURE)

| Leg | Anchor (file:line : name) | Purity (scanned) |
|---|---|---|
| **★ UNIVALENCE = the faithful self-cover (object = its readings ⟹ equal)** | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:47 : object1_injective` (`Function.Injective Object1`); `:69 : self_covering_closure` | PURE (FlatOntologyClosure **8/0**; `object1_injective`/`self_covering_closure` individually PURE) |
| **★ UNIVALENCE at the reading level = kernel coincidence (equivalent readings ARE equal)** | `lean/E213/Lens/Unified.lean:64 : lensIso_iff_kernel_eq` (`LensIso L M ↔ ∀ x y, L.equiv x y ↔ M.equiv x y`) | PURE (Unified **14/0**) |
| **the identity type's groupoid = the `LensIso` groupoid (refl/symm/trans = refl/⁻¹/·)** | `lean/E213/Lens/Unified.lean:42 : LensIso`, `:46 : lensIso_refl`, `:51 : lensIso_symm`, `:54 : lensIso_trans`; `lean/E213/Lens/LensCore.lean:93 : refines_refl`, `:95 : refines_trans` | PURE (Unified **14/0**, LensCore **11/0**) |
| **Id_A(x,y) = the refinement/equality reading; the fiber** | `lean/E213/Lens/LensCore.lean:48 : Lens.equiv`, `:90 : Lens.refines`; `lean/E213/Lens/Unified.lean:77 : LensFiber` | PURE (LensCore **11/0**, Unified **14/0**) |
| **transport = the Lens 2-cell (M.view = h∘L.view), naturality** | `lean/E213/Lens/Compose/Morphism.lean:37 : view_factors_through_morphism`; `:29 : IsLensMorphism`; `:60 : refines_of_morphism` | PURE (Morphism **3/0**) |
| **path induction (J) = refl-generation + initiality (only arrow out of the free object)** | `lean/E213/Lens/Foundations/UniversalDistinguishing.lean:103 : dhom_unique_pointwise`; `lean/E213/Lens/Foundations/SemanticAtom.lean:412 : raw_initial` | PURE (`dhom_unique_pointwise`, `raw_initial` individually PURE) |
| **★ the iterated Id(Id(…)) = the cell-dimension fold-height tower run UP** | `lean/E213/Theory/Raw/MuNuMirror.lean:80 : succ_not_idempotent`, `:50 : ascent_unbounded` | PURE (MuNuMirror **8/0**) |
| **well-founded descent (the tower terminates at atoms)** | `lean/E213/Theory/Raw/Lambek.lean:199 : isPart_wf`, `:273 : no_infinite_descent` | PURE (Lambek, prior-scan **22/0**) |
| **★ the ∞ (types as ∞-groupoids) = the identity tower never closes (residue re-enters)** | `lean/E213/Lens/Foundations/ResidueReentry.lean:85 : residue_perpetually_reenters`, `:63 : residue_reentry_never_closes` | PURE (ResidueReentry **14/0**) |
| **★ HITs = the Quot-FREE quotient-with-paths (kernel as path-data)** | `lean/E213/Lens/Unified.lean:163 : LensImage.proj_val_eq_iff` (`(proj L x).val = (proj L y).val ↔ L.equiv x y`); `lean/E213/Lib/Math/Algebra/Group/FreeReduction.lean : free_group_quotient_no_quot` (no `Quot`/`Classical`/Mathlib) | PURE (Unified **14/0**; FreeReduction **26/0**, prior-scan) |
| **the (-1)-type/prop = the PURE Bool/decide corner (propext-free)** | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:52–56` (`object1_injective` via `of_decide_eq_true`, NOT `decide_eq_true_eq` which "pulls `propext`"); `FlatOntology.Object1 = decide(s=r)` | PURE (FlatOntologyClosure **8/0**) |
| **the q=±1 residue tag (escape/converge, ∓1; univalent = converge pole)** | `lean/E213/Lib/Math/Foundations/ResidueTag.lean:86 : multiplier_unimodular`, `:133 : escape_residue_outside`, `:160 : converge_residue_fixed`, `:180 : golden_is_converge`, `:228 : residue_tag_two_poles` | PURE (ResidueTag **55/0**) |
| escape residue's kernel (the q=−1 tower / non-trivial identity delegates here) | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective` | PURE |

**Fresh scan tallies this session (`tools/scan_axioms.py`, repo root, `E213.` prefix):**
`E213.Lens.Foundations.FlatOntologyClosure` **8/0** (`object1_injective`, `object1_not_surjective`,
`self_covering_closure` each PURE); `E213.Lens.Unified` **14/0** (`lensIso_iff_kernel_eq`,
`LensImage.proj_val_eq_iff`, `LensIso`, `lensIso_refl/symm/trans` PURE); `E213.Lens.Compose.Morphism`
**3/0** (`view_factors_through_morphism`, `refines_of_morphism` PURE); `E213.Lens.LensCore` **11/0**
(`refines_refl`, `refines_trans` PURE); `E213.Theory.Raw.MuNuMirror` **8/0** (`succ_not_idempotent`,
`ascent_total_descent_partial`, `descent_wf_ascent_unbounded` PURE); `E213.Lib.Math.Foundations.ResidueTag`
**55/0** (`residue_tag_two_poles`, `multiplier_unimodular` PURE); `E213.Lens.Foundations.ResidueReentry`
**14/0** (`residue_perpetually_reenters` PURE). Prior-scan (cited in `infinity_categories.md`/
`homotopy_theory.md` this batch, re-used): `Theory.Raw.Lambek` **22/0**,
`Lib.Math.Algebra.Group.FreeReduction` **26/0**, `dhom_unique_pointwise`/`raw_initial` individually PURE.
All load-bearing anchors PURE.

---

## Dropped / flagged (honest — NOT cited as anchors)

- **The named `IdentityType` / `Id_A` / `univalence` / `pathInduction` / `transport` / `HigherInductive`
  / `HIT` / `isProp` / `isContr` / `hLevel` / `truncation`-type object — ABSENT, predicted-not-built.**
  Grep over `lean/E213` (case-insensitive) for `univalen`, `IdentityType`, `path_induction`/`pathInduction`,
  `HigherInductive`, `\bHIT\b`, `isProp`/`isContr`/`hLevel` returns **zero genuine HoTT matches** — the
  `id`/`Id` token hits are `idLens`/`id`-function false-friends (`Identity.lean`, `DepthJoin`,
  MVT `id_at_*` witnesses), and the `truncation` hits are unrelated (`Real213` cut truncation,
  `CutExpFiniteTruncation`, Steenrod, etc.). So the HoTT bundle is genuinely absent; only its legs (the
  identity-as-refinement reading, the `LensIso` groupoid, the faithfulness theorem, the 2-cell transport,
  the fold-height tower, the `Quot`-free quotient, the q=±1 pole) are built.

- **★ `GRA/HoTT.lean` is a NUMERICAL FALSE-FRIEND — confirmed NOT real HoTT.** `lean/E213/Lib/Math/Algebra/GRA/HoTT.lean`
  exists, but it is the GRA (2,3)-graded-ring "reading R₃" instance: carrier = truncation-LEVEL = ℕ
  (`HoTTCarrier := Nat`), `hottGrade n = n`, `hottOplus = a+b` (suspension grades add), `hottDepth n =
  (n+2)/3`, with theorems `hott_coprime : gcd213 2 3 = 1`, `hott_reach`, `hott_greedy` — the "homotopy
  Chicken McNugget" gcd(2,3)=1-generates-ℕ≥2 numerology. It has **no identity types, no univalence, no
  path induction, no transport, no HITs** — it is the (2,3)-numerical avatar wearing the HoTT name, not the
  homotopy interpretation of type theory. NOT cited as an anchor for any HoTT leg.

- **Higher-coherent univalence as a propositional path-`Equiv` of types-as-∞-groupoids — NOT built (the
  propext/funext ceiling).** The calculus's univalence (`object1_injective`/`lensIso_iff_kernel_eq`) is the
  1-categorical/setoid kernel-coincidence (PURE); the full `(A≃B) ≃ (A=B)` with propositional `Equiv`s on
  both sides needs `funext`/`propext`/`Quot.sound`, forbidden by the repo. The CONTENT (equivalent ⟹
  equal) is PURE at the setoid altitude; the higher-coherent version is the deliberate constructive
  boundary (`equivalence.md`'s stated ceiling; `SYNTHESIS.md` §5 item 4). The propositional truncation
  `‖A‖₋₁` and the classical `Prop`-connectives turn DIRTY at the same wall.

- **The homotopy interpretation (types ≅ spaces / Kan complexes) as a stated model — prose-only.** The
  all-invertible `LensIso` groupoid (q=+1) is the right analogue, but there is no `Space`/`SimplicialSet`/
  `Kan` model object — the same ambient-space absence `infinity_categories.md`/`homotopy_theory.md`/
  `knots.md` Side B located (the colimit/`q=−1` corner).

- **General (non-confluent/undecidable) HITs — Side B, theorem-grade absent.** The `Quot`-free quotient
  builds HITs for the confluent+terminating/decidable corner (`LensImage`/`FreeReduction`); general higher
  inductive presentations (undecidable word problem, Novikov–Boone-grade) are the recurring colimit/isotopy
  break (`SYNTHESIS.md` §5 item 1, Side B), not a fresh gap.

### Verified buildable witness (named, not asserted)
A **"univalence-at-the-setoid-level"** bridge theorem is buildable ∅-axiom from existing PURE legs: state
that *equivalence of readings IS equality of their induced identity types* — i.e. wire
`lensIso_iff_kernel_eq` (`Unified.lean:64`) directly to `object1_injective` (`FlatOntologyClosure.lean:47`)
as a single named lemma `univalence_setoid : LensIso L M ↔ (the kernels — the identity types — coincide)`,
exhibiting "(A≃B) ⟺ (Id_A = Id_B)" at the 1-categorical altitude. Both halves are already closed PURE
(`lensIso_iff_kernel_eq` in Unified 14/0; `object1_injective` in FlatOntologyClosure 8/0); the witness is
the named bridge. Not built this session; named as the concrete promotion target — the HoTT twin of
`infinity_categories.md`'s `unique_filler_iff_strict_truncation` and `homotopy_theory.md`'s Ho(C)
Σ-quotient. (No unverified `decide`/`native_decide` claim is proposed; both legs are verified PURE.)

### Cross-frame
`curry_howard.md` (KEY — `OBJECT = ⟨C|L⟩` = `⟨term|type⟩`; the substrate IS a type theory; `view=fold`
initiality = path induction's J-rule; `raw_initial`/`dhom_unique_pointwise` shared); `equivalence.md`
(KEY — Id = the one Lens-arrow `Lens.refines`/`LensIso`; iso = kernel coincidence `lensIso_iff_kernel_eq`;
the 1-categorical/setoid ceiling = where higher univalence stops); `infinity_categories.md` (types as
∞-groupoids = the cell-dimension fold-height tower; `succ_not_idempotent`/`ascent_unbounded`/
`residue_perpetually_reenters` shared); `homotopy_theory.md` (Ho(C) localization = the `Quot`-free
`LensImage`/`FreeReduction` Σ-quotient = HITs' Side-A corner); `two_cells.md` (the 2-category of readings;
transport = the 2-cell `view_factors_through_morphism`); `godel.md`/`cardinality.md` (the q=−1 escape
diagonal `object1_not_surjective` = the never-closing identity tower's kernel); `SYNTHESIS.md` §2 ("object
= its readings" = univalence's content; the reflexive theme) + §3 (the q=±1 spine). **VERDICT: EXTEND
(by consolidation) + PREDICTION** — HoTT = (Id = the Lens-refinement equality) + (types as ∞-groupoids =
the path-dimension fold-height tower) + (★ univalence = `object1_injective`/`lensIso_iff_kernel_eq`, the
faithfulness ALREADY a theorem — the calculus HAS univalence, not an import) + (truncation = the
fold-height/PURE-prop levels) + (HITs = the `Quot`-free `LensImage`/`FreeReduction` quotient) — NO new
primitive; univalence is the calculus's own faithfulness, and HoTT is the type-theoretic face of the whole
reflexive Lens framework. The single precise absence: the *named* `IdentityType`/`univalence`/`transport`/
`HIT` bundle + higher-coherent univalence at the propext/funext ceiling.
