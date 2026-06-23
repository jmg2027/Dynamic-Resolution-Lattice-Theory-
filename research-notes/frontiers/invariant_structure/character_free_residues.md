# Frontier sub-note: are the character-free residues all the one diagonal, or is LLPO/choice a second?

**Status**: active (2026-06-23). **Tier**: 1. Parent: `research-notes/frontiers/invariant_structure.md`
Q2 ("the character-free residues — do they ALL reduce to the one Lawvere diagonal, or are some genuinely
independent?"). Anchors: `decomposition/SYNTHESIS.md` §2 finding (iv), §3, §5.1–§5.2;
`decomposition/practice/{cardinality,godel,computability_halting,measure,nonstandard_analysis,
descriptive_set_theory,stone_duality,berkovich_geometry,class_field_theory}.md`.

The invariant inventory has two named invariants: **A** (the character arrow `×↦·`/`×↦+`) and **B** (the
`q=±1` residue tag). The *character-free* residues are the world where **B exists with no A** — there is
no multiplicative reading, only the escape/converge bit (SYNTHESIS §2 (iv), "Independent (foundational
world)"). The question: is that bare-B world a single object (the Lawvere diagonal) or two?

---

## Verdict (one paragraph)

**Two faces of distinct kind, ONE residue at the locus they share — not two independent residues, and not
literally one theorem either.** The Lawvere diagonal is a single **∅-axiom, constructive, *negative*
theorem**: the self-cover of a distinguishing carrier into its own predicate algebra is faithful but never
total (`object1_not_surjective` / `no_surjection_of_fixedpointfree`). Cantor, Gödel, Russell/Liar/Tarski,
and halting are *literally* instances of it (`one_diagonal_generates` packs three; `computability_halting.md`
adds halting as the `B=Bool` "halts" feature) — these genuinely **all reduce to the one diagonal**, proven.
The **LLPO/choice/ultrafilter** point is **NOT** that theorem: it is a non-constructive *principle stated as
a `Prop`* (`LPO`/`WLPO`/`MP`/`LLPO`, `Omniscience.lean`) that the corpus **never proves** and only calibrates
*against*. The cleanest way to see they are not the same object: the diagonal is a theorem 213 **owns**
(0 axioms, derived), whereas LLPO is a hypothesis 213 **refuses** (it is exactly the omniscient sign-decision
the residue declines to make). They meet at one spot — and the meeting is not a coincidence: the LLPO act is
precisely the move that would *totalize/inhabit* the reached-by-none residue the diagonal leaves. So:
**the diagonal is the residue's "internal/constructive face" (the surplus is built and proven outside every
view); LLPO/choice is the residue's "external/strength face" (the omniscient act that would force the surplus
into a verdict).** Option (ii) — *one residue, two faces, distinguished by axiom-status (∅-axiom theorem vs
non-constructive `Prop`)* — is the grounded answer; the bare "(iii) two independent residues" is **wrong** (they
are not independent: LLPO is named *as* the act on the diagonal's surplus), and the bare "(i) all the diagonal"
is **incomplete** (LLPO is not an instance of the diagonal theorem — it is a different status of object).

---

## The two objects, exactly

### Object 1 — the Lawvere diagonal (CONSTRUCTIVE, ∅-axiom, owned)

The single fixed-point engine and its instances. All grep-verified; file:line:name from this session.

- `lean/E213/Lens/Foundations/OneDiagonal.lean:43:lawvere_fixed_point` — point-surjective `f:A→(A→B)` ⟹
  every `t:B→B` has a fixed point.
- `:51:no_surjection_of_fixedpointfree` — contrapositive: a fixed-point-free `t` forbids any
  point-surjection. **The engine.**
- `:61:cantor_via_lawvere` (Bool, `t=not`), `:68:residue_is_lawvere_diagonal` (the `Object1` residue),
  `:87:russell_liar_no_surjection` (Prop, `t=Not` = Russell/Liar/Tarski).
- `:101:one_diagonal_generates` — Cantor (Bool) ∧ Russell/Liar/Tarski (Prop) ∧ the residue's non-closure
  (Raw) as **three instances of one construction `g a := t(f a a)`**.
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:47:object1_injective` (faithful),
  `:61:object1_not_surjective` (never total), `:69:self_covering_closure`,
  `:138:distinguishing_always_leaves_residue` — the residue *as a theorem*, with the named inhabitant
  `undifferentiated` (`:87`, `:92:undifferentiated_not_object1`).

The character-free residues that **are** this theorem (each = the same `g a := t(f a a)`, only the projected
feature differs):

| residue | feature projected | anchor |
|---|---|---|
| Cantor / uncountable | "is one of these" (Bool) | `cardinality.md`; `OneDiagonal:61` |
| Gödel incompleteness | "is provable" (Prop, `t=Not`) | `godel.md`; `OneDiagonal:87` |
| Russell / Liar / Tarski | self-membership / truth (Prop) | `OneDiagonal:87`, `:101` |
| halting | "halts on input" (Bool) | `computability_halting.md`; `OneDiagonal:51` at `B=Bool` |
| Borel⊊analytic / Suslin | projection escapes every level | `descriptive_set_theory.md`; `object1_not_surjective` graded by `Lambek.isPart_wf` / `MuNuMirror.ascent_unbounded` / `DepthHeightDiagonal.lean:56:height_diagonal_escapes` |
| non-measurable set (the *shape*) | the Vitali selector's diagonal | `measure.md`; `object1_not_surjective` |

These all **reduce to the one diagonal** — proven for Cantor/Gödel/Russell/Liar/Tarski (`one_diagonal_generates`,
∅-axiom), and as a *decomposition reading* (engine reused, named object often absent) for halting / Suslin /
non-measurable. This half of Q2 is answered **yes, all the diagonal**.

### Object 2 — the LLPO / choice / ultrafilter point (NON-CONSTRUCTIVE, never proved, refused)

The omniscience ledger: principles *stated as `Prop`s*, with ∅-axiom implications **between** them, but no
∅-axiom proof of any of them.

- `lean/E213/Lib/Math/Logic/Omniscience.lean:25:LPO`, `:28:WLPO`, `:31:MP`, `:35:LLPO` (definitions);
  `:40:lpo_imp_wlpo`, `:48:lpo_imp_mp`, `:59:lpo_iff_wlpo_and_mp` (the ledger's internal deductions, ∅-axiom).
- `lean/E213/Lib/Math/Logic/LLPO.lean:59:lpo_imp_llpo`, `:81:wlpo_imp_llpo` (LPO⟹LLPO, WLPO⟹LLPO).
- `lean/E213/Lib/Math/Logic/RealDichotomyLLPO.lean:517:RealDichotomy` (def: every corpus real is `≤1` or `≥1`),
  `:525:llpo_of_realDichotomy` (the real sign dichotomy ⟹ LLPO), `:539:encodedDichotomy_of_llpo` (converse —
  the two-sided calibration: *the sign-decision IS exactly LLPO*).
- `lean/E213/Lib/Math/Logic/RealComparabilityLLPO.lean:33:comparability_imp_llpo` (comparability of any two
  corpus reals ⟹ LLPO — "not constructively totally ordered").
- `lean/E213/Lib/Math/Logic/BolzanoWeierstrass.lean:197:lpo_of_bw` (the same ledger: BW ⟹ LPO).

The crucial structural fact, in `Omniscience.lean:9-13` verbatim: an omniscience principle is the
**"freeze a transition into a verdict" move the residue refuses** — *"213 does not prove these; it states
them as `Prop`s and calibrates everything against them."* That is the opposite stance to the diagonal,
which 213 **proves**.

The five calibrated boundaries (SYNTHESIS §5.2) — all said to "converge on the one ultrafilter/LLPO/choice
point" — are five places this *same* Object 2 is the irreducible remainder:

1. **Non-standard analysis** (`nonstandard_analysis.md`): the non-principal ultrafilter `𝒰`'s maximality
   totalizes the order = `comparability_imp_llpo` → `llpo_of_realDichotomy`. Internal horn (cofinite quotient
   `Hyper213`, 7/0) is built; the ultrafilter is the LLPO-strength exterior, no witness.
2. **Descriptive set theory** (`descriptive_set_theory.md`): Borel/projective determinacy + projective-level
   perfect-set need **large cardinals / Choice** — the large-cardinal analogue of the ultrafilter's LLPO.
3. **Stone duality** (`stone_duality.md:41-46`): the Stone space `Spec(B)` = ultrafilters on `B`; Stone's
   theorem for arbitrary Boolean algebras = **BPI** (a choice fragment) = the *same* non-principal ultrafilter.
   Boolean side built (`Order/BooleanAlgebra.lean`).
4. **Berkovich geometry** (`berkovich_geometry.md`): "these are ALL the multiplicative seminorms" = the same
   LLPO totalization (twin of p-adic Ostrowski exhaustiveness).
5. **Class field theory** (`class_field_theory.md`): milder kind — the global `ArtinMap`/idele/adele *bundle*
   absent; local per-prime `q±1` Frobenius built (`FP2SqrtD`, 32/0).

All five **collapse to one locus** (SYNTHESIS §5.2 closing): the non-principal-ultrafilter/LLPO/choice point,
not five separate gaps. So Object 2 is **one** object (one obstruction wearing five field-names), just as
Object 1 is one engine wearing many field-names.

---

## Why they are the SAME residue (two faces), not two independent ones

The decisive evidence against "(iii) two independent character-free residues" is that **Object 2 is named
directly in terms of Object 1's output**, in two corpus places:

- `nonstandard_analysis.md` finding (3): the ultrafilter `𝒰` is *"precisely the device that inhabits"* the
  reached-by-none residue — it *"collapses 'the sequence points below everything' (a pointing, `q=±1`) into
  '`[(1/n)]` is a number.'"* I.e. LLPO/`𝒰` is the act that would turn the diagonal's **reached-by-none
  surplus** (`object1_not_surjective` — outside every view's image) into an **inhabited verdict**. The two
  objects are about the *same surplus*: the diagonal *produces* it (constructively, as a proven remainder),
  LLPO would *resolve* it (non-constructively, by an omniscient choice).
- `Omniscience.lean:9-13`: LLPO is the "freeze a transition into a verdict" move *the residue refuses* —
  defined by reference to the residue. It is the residue's negation-of-refusal, not a separate residue.

So the relation is **internal face ↔ external/strength face of one thing** (option ii):

| | diagonal (Object 1) | LLPO/choice (Object 2) |
|---|---|---|
| logical status | **theorem** (proven) | **`Prop` hypothesis** (never proven) |
| constructivity | ∅-axiom, constructive | non-constructive (the omniscient act) |
| polarity | universal **negative** (`¬ Surjective`) | the **decision** it would take to defeat that negation |
| 213's stance | **owns** it (derived) | **refuses** it (calibrates against) |
| what it does to the surplus | *produces* reached-by-none surplus | would *inhabit/totalize* the surplus |
| one object, many names | Cantor/Gödel/Russell/Liar/halting/Suslin | ultrafilter/BPI/large-cardinal/Stone-Spec/Berkovich |

These are dual faces of the residue tag B's two poles read foundationally: the diagonal is the **`q=−1`
escape pole proven** (the surplus oscillates outside every image, `no_surjection_of_fixedpointfree`); LLPO is
the **act that would force a `q=+1`-style verdict** on that escape (totalize the order, decide every `S⊆ℕ`,
inhabit the infinitesimal). The `q=±1` tag is *one* invariant (B); the diagonal and LLPO are its
proven-escape side and its would-be-totalizing side.

## The cleanest distinguishing criterion

> **Axiom-status under `#print axioms`.** The diagonal is the unique character-free residue that is a
> **`∅`-axiom theorem** (built, constructive, derived — `no_surjection_of_fixedpointfree` /
> `object1_not_surjective`). The LLPO/choice/ultrafilter point is the unique character-free residue that is a
> **non-constructive `Prop` with no `∅`-axiom witness** (stated and calibrated against, never proved —
> `LPO`/`LLPO` in `Omniscience.lean`). Equivalently, by **polarity + reachability**: the diagonal is the
> *negative* theorem that the surplus is **reached by none**; LLPO is the *positive omniscient act* that
> would **reach it** (totalize/inhabit). One produces the residue, the other would resolve it.

A sharper one-line test for any candidate character-free residue: **does 213 prove it (∅-axiom) or refuse it
(state-as-`Prop`)?** Proves ⟹ it is the diagonal (or an instance). Refuses ⟹ it is the LLPO/choice face.
Nothing in the corpus sits in a third box.

## Measure-theoretic q=−1 specifically (the prompt's sub-question)

The non-measurable / Vitali escape is **the diagonal in *shape*, the choice point in *what builds it***
(`measure.md` §LEVERAGE). The non-measurable set IS the `q=−1` diagonal of the weight-reading's *uncountable*
self-cover (`object1_not_surjective` / `no_surjection_of_fixedpointfree` — Object 1). But the *operation that
constructs the uncountable selector* is the Axiom of Choice (Object 2). So measure splits the two faces
cleanly on one object: the **pathology's shape = the diagonal**; the **dividing line (why the repo can avoid
it) = the choice/LLPO point**. The repo lives in the `q=+1` finite-`List` corner (no uncountable selector ⟹
the diagonal cannot arise, `MeasurableSet.lean:9`). This is the same internal-face/external-face split as
non-standard analysis, on a different field — confirming the two-faces verdict rather than a third residue.

---

## BUILT vs ABSENT / conjectural (no false witnesses)

**BUILT, ∅-axiom (grep-verified file:line this session; counts as recorded in the cited corpus notes):**
- The diagonal engine + instances: `OneDiagonal.lean:43/:51/:61/:68/:87/:101` (corpus tally 11/0),
  `FlatOntologyClosure.lean:47/:61/:69/:138` (corpus tally 7/0).
- The omniscience ledger: `Omniscience.lean:25/:35/:40/:59` (8/0), `LLPO.lean:59/:81`,
  `RealDichotomyLLPO.lean:517/:525/:539` (31/0), `RealComparabilityLLPO.lean:33` (2/0),
  `BolzanoWeierstrass.lean:197:lpo_of_bw`.
- Diagonal-graded-by-height (descriptive set theory's escape): `DepthHeightDiagonal.lean:56`,
  `MuNuMirror.lean:50:ascent_unbounded`.
- Internal hyperreal horn: `Hyper213.lean` (cofinite quotient, 7/0); Boolean side of Stone:
  `Order/BooleanAlgebra.lean` (25/0); CFT local Frobenius: `FP2SqrtD` (32/0).

**ABSENT (predicted-not-built / deliberately-never-built):**
- No `Ultrafilter`/`ultrafilter` object, no `transfer`/`Łoś`/`losTheorem`, no `standardPart`/`halo`
  (`nonstandard_analysis.md` "Dropped/flagged", grep-confirmed empty there). The ultrafilter's maximality
  is the LLPO-strength exterior with **no ∅-axiom witness** — named, not built.
- No `Vitali`/non-measurable-set object (deliberately never built — finite `List`, `measure.md`).
- No `Suslin`/`Wadge`/`determinacy`/`perfect_set` object; Borel/projective **determinacy** flagged as the
  large-cardinal/Choice boundary (`descriptive_set_theory.md:124`, grep-confirmed absent there).
- No `Stone Spec(B)` reconstruction object; no Berkovich `M(A)` object — both the LLPO/BPI exterior.
- LLPO itself is a **`Prop` 213 never proves** — present as a *hypothesis carrier*, ABSENT as a theorem.

**Honest caveat on tallies.** The `N/0` PURE counts above are *as recorded in the cited corpus notes*
(`nonstandard_analysis.md`, `measure.md`, SYNTHESIS §4). I re-grep-verified every file:line:name in this
note against the live tree; I did **not** re-run `tools/scan_axioms.py` to fresh-confirm the counts this
session (`scan_axioms.py` returned `0 pure / 0 dirty` for the module paths I tried, i.e. it needs built
artifacts / a different invocation than I had). The *line numbers and theorem names are live-verified*; the
*axiom-purity tallies are inherited, not re-scanned* — flagged so as not to be a false witness.

---

## Net

Q2 answer: **the character-free residues are NOT all independent, and they are NOT all literally the one
diagonal theorem either.** There are exactly **two faces of one residue**: (1) the **Lawvere diagonal** —
the constructive ∅-axiom theorem 213 *owns*, into which Cantor/Gödel/Russell/Liar/Tarski/halting (and, as
readings, Suslin / non-measurable-shape) **all genuinely reduce**; and (2) the **LLPO/choice/ultrafilter
point** — the single non-constructive `Prop` 213 *refuses*, onto which the five calibrated boundaries
(non-standard analysis, descriptive set theory, Stone, Berkovich, class field) **all converge as one locus**.
They are the **internal/constructive face** and the **external/strength face** of the same `q=±1` residue:
the diagonal *produces* the reached-by-none surplus; LLPO is the omniscient act that would *inhabit* it.
Distinguishing criterion: **∅-axiom theorem (diagonal) vs non-constructive `Prop`-never-proved (LLPO)** —
equivalently, *reached-by-none-proven* vs *the-act-that-would-reach-it*.
