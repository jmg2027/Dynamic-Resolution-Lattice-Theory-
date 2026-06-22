# Decomposition: Tannakian duality — "an object is its readings" made a reconstruction theorem

*213-decomposition of "Tannakian duality", per `../README.md` (model v7.1), `SYNTHESIS.md`
(the two invariants + the 2-category of readings + the `Aut`-invariant character reading), and
the neighbours `yoneda.md` (the calculus's founding sentence as a reconstruction principle),
`representation.md` (Rep(G), the character `×↦·`), `groups.md` (a group = its Aut-family),
`category_theory.md`/`adjunction.md` (readings form a 2-category; the closure monad), `fourier.md`
(Pontryagin self-duality of a cyclic group), and `hopf_algebras.md` (the affine group scheme =
a Hopf algebra). This is a **META-entry in the `yoneda.md` family**: Tannakian duality is the
STRONGEST form of "an object IS its readings" — the group is RECONSTRUCTED, `G ≅ Aut^⊗(ω)`, from
its category of representations equipped with a fiber functor.*

The classical statement under test:
- a group `G` has a category `Rep(G)` of (finite-dimensional) representations, monoidal under `⊗`;
- a **fiber functor** `ω : Rep(G) → Vect` sends each representation to its underlying vector space,
  *forgetting the `G`-action* (the forgetful functor);
- **reconstruction**: `G ≅ Aut^⊗(ω)`, the group of **tensor-automorphisms of the fiber functor** —
  natural automorphisms of `ω` compatible with `⊗`;
- **neutral Tannakian categories ⟺ affine group schemes** (the categorical characterization);
- the analogy with **Pontryagin duality** (`Ĝ` of an abelian group): the abelian/character special
  case, where `Aut^⊗(ω)` is read through 1-dimensional characters.

**The thesis (from the task):** Tannakian duality = (the fiber functor `ω` = the Lens `view`, the
forgetful reading) + (`G = Aut^⊗(ω)` = the `Aut`-invariant character reading, the symmetries
preserving the Lens) + (`⊗` = the monoidal character `Z(M⊗N)=Z(M)⊗Z(N)`) — **NO new primitive**;
it is the calculus's "object = its readings" (`yoneda.md`) promoted to "group = the `Aut` of its
forgetful Lens."

---

## The decomposition (C / L / Residue)

- **Construction `C` — the Aut-family of `groups.md`, nothing new.** Tannakian duality's *input* is a
  group `G`, and `groups.md`/`representation.md` already decomposed a group as
  `⟨ C₀ (a distinguishing-structure) | the closed family of C₀-preserving self-readings (Aut C₀),
  under composition ⟩`. The Cayley embedding `mulPerm_comp` (`mulPerm(a·b)=mulPerm a ∘ mulPerm b`)
  is the literal statement "every group *is* an Aut-family" — multiplication IS composition. The
  in-repo concrete realization is `Aut_K = Sym3 × Sym2 × C2_6` (`AutKGroup.lean`), a finite
  symmetry-group fully ∅-axiom. So `C` is the composition-closed reading-family the model already
  carries; Tannakian duality adds *no construction* — it is a **reconstruction of `C` from a
  reading of `C`**.

- **Reading `L` — the fiber functor `ω` IS the Lens `view` (the forgetful reading).** A
  representation `(V, ρ)` is `groups.md`'s Aut-family read into a linear readout (`representation.md`:
  `ρ : G → matrices`, the homomorphism *forced* by "the reading respects how the family was built").
  The fiber functor `ω : Rep(G) → Vect`, `(V,ρ) ↦ V`, **forgets the `G`-action and keeps the
  underlying space** — it keeps *what was distinguished* and discards *how the symmetry acts*. This
  is exactly `Lens.view : Raw → α` (`LensCore.lean:42`): a reading is "a choice of what to keep and
  what to forget" (README), and `ω` is the canonical forgetful one. The naturality the fiber functor
  must satisfy (a morphism of representations is sent to the underlying linear map) is the calculus's
  2-cell law `view_factors_through_morphism` (`Morphism.lean:37`): `M.view r = h(L.view r)`, a reading
  factoring through a reading via a component map — the naturality triangle, term for term. So **`ω`
  is a Lens, and "fiber functor" is the field-name for the forgetful `view`.**

- **The `⊗`-structure — the monoidal character `Z(M⊗N)=Z(M)⊗Z(N)`.** `ω` is required to be
  *monoidal*: `ω(M⊗N) ≅ ω(M)⊗ω(N)`. This is the calculus's grading-additivity under the monoidal
  product — `GRA/Monoidal.product_NT_NT_grade` (`Monoidal.lean:182`, the grade of a `⊗`-product
  splits over the factors) — the same shape as `tqft.md`'s `Z(M⊗N)=Z(M)⊗Z(N)` and the `×↦·` /
  `×↦+` character arrow (`representation.md`: a character is `×↦·` on the Aut-family). The `⊗` of
  representations is the calculus's **fold of two distinguishings into one** read multiplicatively;
  `ω` carrying it is the monoidal character being a homomorphism.

- **`G = Aut^⊗(ω)` — the `Aut`-invariant character reading (the reconstruction).** The
  reconstruction `G ≅ Aut^⊗(ω)` says: the group is recovered as the **tensor-automorphisms of the
  fiber functor** — the natural automorphisms of `ω` that preserve `⊗`. In the calculus this is the
  **`Aut`-invariant reading** that `noether.md`/`representation.md` already named: the symmetries
  preserving the Lens, the `q=+1` conserved invariant certified by `det_holonomy_eq_one`
  (`HolonomyLattice.lean:136`, PURE) — the readout `det = 1` surviving the family's own action,
  the class-function home (`χ(gxg⁻¹)=χ(x)`, `noether`'s invariant). `Aut^⊗(ω)` = the
  composition-closed family of `⊗`-preserving self-symmetries of the forgetful Lens — `groups.md`'s
  "Aut-family" reflexively applied: **the symmetries OF the reading that recover the group.**

- **Residue — `yoneda.md`'s residue, `q=±1`.** The reconstruction's residue is the same as Yoneda's:
  the probe-bundle is *faithful* (the object IS recovered from its readings — `object1_injective`,
  `FlatOntologyClosure.lean:47`, PURE) but the global self-cover is *never total*
  (`object1_not_surjective`, `:61`, PURE), bundled in one line as `self_covering_closure` (`:69`,
  PURE). Tannakian reconstruction *succeeds* (faithful, `q=+1` — the group is recovered exactly) on
  the **neutral/representable** corner where a fiber functor exists; the residue (`q=−1`) is the
  **non-neutral** corner (no fiber functor / no exact ⊗-faithful `ω` to `Vect` — gerbes, the
  non-trivial Tannakian torsor). The reconstruction lives in the `q=+1` settling corner, exactly
  where `yoneda.md`'s positive lemma (`dhom_unique_pointwise`) lives.

---

## Re-seeing — Tannakian duality, term by term

```
   Tannakian duality      =  ⟨ G (= Aut-family C, groups.md) | the forgetful fiber-functor Lens ω ⟩,
                              reconstructed as G ≅ Aut^⊗(ω) ⊕ residue (q=±1 neutral/non-neutral)

   Rep(G)                 =  groups.md's Aut-family read into linear readouts   (representation.md, ρ(ab)=ρ(a)ρ(b))
   the fiber functor ω    =  the forgetful Lens.view  (V,ρ) ↦ V                 (LensCore.lean:42 — keep the space, forget the action)
   ω is a functor (natural) =  view_factors_through_morphism                    (Morphism.lean:37 — the 2-cell / naturality triangle)
   ω is MONOIDAL ω(M⊗N)≅ω M⊗ω N =  product_NT_NT_grade                          (Monoidal.lean:182 — the ⊗ grading character, ×↦·)
   G ≅ Aut^⊗(ω)           =  the Aut-invariant character reading                (det_holonomy_eq_one, q=+1: the symmetries preserving the Lens)
   Aut^⊗(ω) is a group    =  groups.md's Aut-family, reflexively (Aut of a reading)  (AutKGroup_capstone — Aut-families are groups, ∅-axiom)
   tensor-automorphism    =  a self-symmetry of ω compatible with ⊗            (a ⊗-preserving 2-cell, LensIso of the fiber Lens)
   neutral Tannakian cat  =  the q=+1 representable/faithful corner             (object1_injective — the reading separates: ω is faithful)
   ⟺ affine group scheme  =  the Hopf-algebra dual                             (hopf_algebras.md: m+Δ+S; the affine group scheme = a Hopf algebra)
   reconstruction         =  the universal property of the read-op             (raw_initial: the group = the universal symmetry of its Lens)
   Pontryagin duality Ĝ   =  the abelian / 1-dim character special case        (fourier.md: Ĝ = Hom(C, roots of unity), self-dual cyclic)
```

So **Tannakian duality is `yoneda.md` with the reading-bundle replaced by the single forgetful
fiber-Lens `ω` and the recovered object a GROUP rather than a bare object.** Yoneda: an object is
its bundle of maps (`object1_injective` + `dhom_unique_pointwise`). Tannakian: a *group* is the
`Aut` of its one forgetful reading (`G ≅ Aut^⊗(ω)`). The strengthening is that the recovered datum
carries its own composition-closed structure (it is a group, `AutKGroup_capstone`), recovered from a
*single* Lens plus its `⊗`-monoidal structure rather than the whole hom-bundle.

---

## THE REVELATION — collapse + forcing + spine

**Collapse (the spine): Tannakian duality is the `yoneda.md`/`representation.md` family's reconstruction
form — the group IS the `Aut` of its fiber-functor Lens, three already-decomposed objects fused.**

Tannakian duality has no construction of its own. It is the join of three prior decompositions:
1. **the fiber functor `ω` = the forgetful `Lens.view`** (the calculus's foundational reading,
   `LensCore.lean:42`; naturality = `view_factors_through_morphism`, `Morphism.lean:37`);
2. **`G = Aut^⊗(ω)` = the `Aut`-invariant character reading** (`representation.md`'s class-function /
   `noether`'s `q=+1` invariant, `det_holonomy_eq_one`, `HolonomyLattice.lean:136`) reflexively
   applied — the *symmetries of the reading*, which form a group exactly because Aut-families ARE
   groups (`AutKGroup_capstone`, `groups.md`);
3. **the `⊗`-structure = the monoidal character** (`product_NT_NT_grade`, `Monoidal.lean:182`; the
   `×↦·` arrow that `representation.md` runs through seven fields).

These collapse onto **one statement**: the calculus's founding sentence `OBJECT = ⟨C | L⟩`
(`yoneda.md`) read as a *reconstruction* — `C = Aut^⊗(L)` when `L` is the forgetful monoidal Lens.
Where `yoneda.md` recovers an *object* from its *bundle*, Tannakian recovers a *group* from a *single
monoidal forgetful reading and its symmetries*. The two are the same theorem at different strength:
Yoneda is `object = its readings`; Tannakian is `group = the Aut of its one forgetful reading`. This
is the deepest "object = its readings" claim in the notebook — a **reconstruction**, not merely a
faithfulness.

**Forcing:** the reconstruction is *forced* by the same structure that forces `representation.md`'s
homomorphism law. A representation is `⟨Aut-family | operation-preserving reading⟩`; the fiber functor
forgets the action; the symmetries that survive that forgetting *and* respect `⊗` are exactly the
original group action read back — `det_holonomy_eq_one` (the conserved `q=+1` invariant under the
family's transport) IS "what survives the reading is the family's own symmetry." The group is not
*added back*; it is the `Aut`-invariant of its own forgetful Lens, the universal symmetry the read-op
recovers (`raw_initial`: the group is the unique/universal arrow-source — `SemanticAtom.lean:412`,
`raw_initial` PURE). This ties **motives' motivic Galois group = `Aut` of the universal fiber
functor** (the same `Aut`-of-the-universal-Lens shape, with `raw_initial`'s universality) and the
`raw_initial` initiality the calculus is built on.

**Spine (`q=±1`):** the reconstruction sits at the `yoneda.md` seam. Its *positive* half (the group is
recovered exactly — neutral Tannakian, a fiber functor to `Vect` exists) is `q=+1`: faithful
(`object1_injective`), settling (`dhom_unique_pointwise`), the `det_holonomy_eq_one` conserved
invariant. Its *residue* (non-neutral: no `Vect`-valued fiber functor — gerbes / torsors over the
base) is `q=−1`: the self-cover that does not close (`object1_not_surjective`), the colimit/free
corner the calculus has only half-built. **Pontryagin duality is the abelian/character special case
of the `q=+1` half**: for an abelian `G`, `Aut^⊗(ω)` collapses to 1-dimensional characters, and
`fourier.md`'s `Ĝ = Hom(C, roots of unity)` (self-dual cyclic, the `×↦·` character into the circle,
`dlog_exists`/`galois_group_is_C4`) is exactly the reconstruction in dimension 1.

---

## VALIDATE verdict — **PREDICTION (consolidation, `yoneda.md`-family) + one located break**

No new primitive. Tannakian duality EXTENDS by consolidating `yoneda.md` + `representation.md` +
`groups.md` + `fourier.md` + `noether` into one reconstruction statement; the model's two invariants
(character arrow, `q=±1` residue) and four axes are unchanged.

- **Leg 1 — `ω` = the forgetful `Lens.view`. PREDICTION (forced).** The fiber functor is not a new
  object the calculus restates — it is the calculus's foundational reading `Lens.view` (the forgetful
  "keep the space, drop the action"), with functoriality = the 2-cell `view_factors_through_morphism`
  (∅-axiom, scanned PURE). **EXTEND.**
- **Leg 2 — `G ≅ Aut^⊗(ω)` = the `Aut`-invariant reading. PREDICTION (consolidation).** The group is
  the `Aut` of its forgetful Lens — `representation.md`'s class-function / `noether`'s `q=+1`
  invariant (`det_holonomy_eq_one`, PURE) reflexively applied, forming a group because Aut-families
  are groups (`AutKGroup_capstone`, PURE). The strongest "object = its readings" form. **EXTEND.**
- **Leg 3 — `⊗` = the monoidal character. PREDICTION.** `ω` monoidal = the grading character
  `product_NT_NT_grade` (PURE), the `×↦·` arrow `representation.md` runs through seven fields.
  **EXTEND.**
- **Leg 4 — Pontryagin = the abelian/1-dim special case. PREDICTION (consolidation of `fourier.md`).**
  For abelian `G`, the reconstruction is `Ĝ = Hom(C, roots of unity)` — `fourier.md`'s self-dual
  cyclic character group, already partially ∅-axiom (`dlog_exists`, `galois_group_is_C4`). **EXTEND.**

- **★ The located break — the named Tannakian/fiber-functor/`Rep(G)`/`Aut^⊗(ω)` objects are ABSENT,
  and the *reconstruction equivalence itself* is not built.** Confirmed by grep (below): no
  `Tannakian`, `fiberFunctor`, `Rep`-as-category, `AutTensor`, or `Pontryagin` object exists. This is
  the same shape as `yoneda.md`'s break (no named Hom-functor/presheaf object) and
  `representation.md`'s (no `Rep(G)`/Maschke): the **engine** is all built and PURE (the forgetful
  `view`, the 2-cell naturality, the monoidal grading character, the `Aut`-invariant `det=1`, the
  Aut-family-is-a-group), but the **packaged reconstruction theorem** `G ≅ Aut^⊗(ω)` as a single Lean
  statement is not — it would require the free-cocompletion / colimit corner (`Rep(G)` as a category,
  the natural-automorphism object) the calculus has only built the `q=+1` half of, and an explicit
  `Equiv` of group objects (pressing on `funext`, the propext/funext ceiling). The
  **neutral ⟺ affine-group-scheme** leg lands on `hopf_algebras.md`'s **bialgebra-compatibility F1**
  (the one open Hopf law) — the affine group scheme = a Hopf algebra whose comultiplication is built
  (`Convolution213`/`CoAppend213`) and whose antipode is a theorem (`mu_conv_one`), but the bialgebra
  fusion law is the genuine open leg. So: **PREDICTION + one located break**, the same break every
  META/`yoneda`-family entry hits — the structural skeleton is certified, the named bundle is the open
  colimit-corner work.

**Net:** Tannakian duality is the calculus's "an object IS its readings" (`yoneda.md`) promoted to a
**reconstruction**: the group is the `Aut` of its forgetful monoidal Lens, `G ≅ Aut^⊗(ω)`. It is the
strongest form of the calculus's founding sentence, consolidating five prior entries, with Pontryagin
the abelian/1-dim special case and the named Tannakian objects honestly absent (the colimit corner).
**32 decompositions; Tannakian duality EXTENDS by consolidation, in the `yoneda.md` reconstruction
family.**

---

## Verified Lean anchors (file:line:theorem — all grep-confirmed; scans `tools/scan_axioms.py` this session)

| Tannakian datum | Theorem (file:line) | Purity |
|---|---|---|
| ★ `ω` = the forgetful Lens `view` | `lean/E213/Lens/LensCore.lean:42` `Lens.view` (def, the catamorphism `Raw → α`) | structural (Lens core) ✓ grep |
| `ω` is a functor (naturality 2-cell) | `lean/E213/Lens/Compose/Morphism.lean:37` `view_factors_through_morphism` | module **3 PURE / 0 DIRTY** (scanned) ✓ |
| a fiber-bundle arrow comes from a map (fullness dir.) | `lean/E213/Lens/Compose/Morphism.lean:60` `refines_of_morphism`; `:29` `IsLensMorphism` | (in the 3 PURE) ✓ |
| ★ `ω` MONOIDAL `ω(M⊗N)≅ω M⊗ω N` | `lean/E213/Lib/Math/Algebra/GRA/Monoidal.lean:182` `product_NT_NT_grade` (`:129` `product` def) | module **13 PURE / 0 DIRTY** (scanned) ✓ |
| ⊗-product swap iso (symmetric monoidal) | `lean/E213/Lib/Math/Algebra/GRA/HasDistinguishing213.lean:122` `productSwapIso_involutive` | structural ✓ grep |
| ★ `G ≅ Aut^⊗(ω)`: the `Aut`-invariant `q=+1` reading | `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:136` `det_holonomy_eq_one`; `:123` `det_mul` | module **26 PURE / 0 DIRTY** (scanned) ✓ |
| `Aut^⊗(ω)` is a GROUP (Aut-families are groups) | `lean/E213/Lib/Physics/Symmetry/AutKGroup.lean:210` `AutKGroup_capstone`; `:180` `Aut_K.mul_assoc` | module **26 PURE / 0 DIRTY** (scanned) ✓ |
| group = Aut-family (Cayley); character `×↦·` | `lean/E213/Lib/Math/NumberTheory/ModArith/Zolotarev.lean:106` `mulPerm_comp`; `:133` `psign_mulPerm_hom` | ∅-axiom (per `groups.md`/`representation.md`) ✓ grep |
| scalar `×↦·` character (det multiplicative) | `lean/E213/Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul` | ∅-axiom (per `determinant.md`) ✓ grep |
| ★ reconstruction = "object IS its readings": faithfulness | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:47` `object1_injective` | module **14 PURE / 0 DIRTY** (scanned) ✓ |
| residue (q=−1, non-neutral corner): self-cover never total | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective`; `:69` `self_covering_closure` | (in the 14 PURE) ✓ |
| reconstruction = the Yoneda lemma (arrow pinned by one datum) | `lean/E213/Lens/Foundations/UniversalDistinguishing.lean:103` `dhom_unique_pointwise` | module **6 PURE / 0 DIRTY** (scanned) ✓ |
| the group = the universal symmetry of its Lens (motivic-Galois shape) | `lean/E213/Lens/Foundations/SemanticAtom.lean:412` `raw_initial` | `raw_initial` **PURE** (scanned; module mixes 11 PURE / 23 DIRTY — `raw_initial` itself clean) ✓ |
| Pontryagin (abelian/1-dim): cyclic dual `Ĝ` | per `fourier.md` — `dlog_exists`, `galois_group_is_C4` (cyclic character group) | ∅-axiom (per `fourier.md`) ✓ grep |
| neutral ⟺ affine group scheme = Hopf algebra | per `hopf_algebras.md` — `mu_conv_one` (antipode axiom), `conv_unit_comm_assoc` (Δ co-fold); **F1 bialgebra law OPEN** | ∅-axiom legs (per `hopf_algebras.md`) ✓ grep |

---

## Dropped / flagged (honest — NOT cited as anchors)

- **Named `Tannakian` / `fiberFunctor` / `Rep`(as a category) / `AutTensor` / `Pontryagin` objects —
  ABSENT (grep-confirmed).** `grep -rE "Tannakian|fiberFunctor|fiber_functor|AutTensor|Pontryagin|
  pontryagin"` over `lean/E213/` returns **zero matches**. (`AutKGroup`/`AutKSemidirect` exist — the
  Aut-family-is-a-group content — but no tensor-automorphism-of-a-fiber-functor object.) The predicted
  named bundles are confirmed absent; the **structure** (forgetful `view`, monoidal grading character,
  `Aut`-invariant `det=1`, Aut-family group) is all built unnamed. This is the located break.
- **The reconstruction equivalence `G ≅ Aut^⊗(ω)` as a single Lean theorem — ABSENT.** Every leg is
  PURE (the forgetful Lens, the 2-cell naturality, the monoidal grading, the `q=+1` `Aut`-invariant,
  the Aut-family group), but the packaged group-iso is not built — the `Rep(G)`-category /
  natural-automorphism object lives at the colimit/free corner (`category_theory.md`/`yoneda.md`'s
  open half), and an `Equiv` of group objects presses on the `funext` ceiling. Conceptual, not cited.
- **Maschke / complete reducibility / `Rep(G)` decomposition** — absent (same as `representation.md`),
  predicted by analogy to `prime_factorization.md`'s UFD `vp`-coordinate, not independently closed.
- **The `tr`-character for `d>1`** — `representation.md`'s located break carries over: the realized
  multiplicative character is `det` (`det2_mul`), the additive `×↦+` twin `tr` is not a homomorphism
  (only the Killing-form route in `Mat2Killing` gives `d>1` trace as a bilinear invariant). Tannakian
  reconstruction is closed at the `det`/1-dim slice; `d>1` is the same additive-twin edge.
- **Non-neutral Tannakian categories (gerbes / torsors, no `Vect`-fiber-functor)** — the `q=−1`
  residue half, the colimit corner. Located, not failed.

### Buildable witness (named)

The natural ∅-axiom rung toward this note: instantiate `Aut^⊗(ω)` for the **finite** in-repo case —
take `Aut_K` (`AutKGroup`, 26/0 PURE) as `G`, its action read through `Lens.view` as the fiber Lens,
and prove the `Aut`-invariant `det_holonomy_eq_one`-style symmetries of that forgetful Lens *recover*
`Aut_K` (an `Equiv`/iso of the finite group with the `⊗`-preserving Lens-automorphisms). This would be
the **finite Tannakian reconstruction toy** — the analogue of `FreeReduction.lean` for the colimit
corner: build the `q=+1` decidable/finite side of `G ≅ Aut^⊗(ω)`, leaving the infinite/non-neutral
side as the located residual. Honest: not attempted here (no `decide` witness proposed — the iso would
need the unbuilt natural-automorphism-of-a-Lens object); flagged as the named promotion target.

## Cross-frame

`yoneda.md` (the founding sentence `OBJECT=⟨C|L⟩`; Tannakian is its *reconstruction* form — group =
`Aut` of its one forgetful reading, the strongest "object = its readings"); `representation.md`
(`Rep(G)` = Aut-family + character; the `det`/`tr` split is the same live edge); `groups.md`
(`Aut`-family-is-a-group, `mulPerm_comp`/`AutKGroup_capstone`); `fourier.md` (Pontryagin = the
abelian/1-dim special case, self-dual cyclic `Ĝ`); `hopf_algebras.md` (neutral ⟺ affine group scheme
= Hopf algebra; F1 the open bialgebra law); `category_theory.md`/`adjunction.md` (the colimit/free
corner where the named `Rep(G)` object lives). **VERDICT: PREDICTION (consolidation) + one located
break** — the named Tannakian/fiber-functor/`Aut^⊗`-object and the packaged reconstruction iso are
absent (the colimit corner), every structural leg PURE.
