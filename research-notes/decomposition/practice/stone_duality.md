# Decomposition: Stone duality — the Bool-valued reading ⟺ its ultrafilter spectrum (a CALIBRATED boundary)

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`). The object:
Stone duality — the contravariant equivalence `BoolAlg ≃ Stone` (Boolean algebras ⇄ compact Hausdorff
totally disconnected spaces), the prime/ultrafilter spectrum `Spec(B)`, the clopen ↔ algebra-element
correspondence, and the distributive-lattice generalization (spectral spaces / Priestley duality). The
thesis to TEST at the REVELATION bar, not re-skin `topos.md`: Stone duality is **the calculus's `Ω=Bool`
reading made a contravariant equivalence with its own spectrum** — a Boolean algebra = the algebra of
Bool-valued readings (`FlatOntology.Object1 = decide(s=r)`, `topos.md`'s Boolean pole), its Stone space =
the spectrum of ultrafilters = the points-reconstructed-FROM-the-readings (the same "object = its readings"
reconstruction as `yoneda.md`/`tannakian_duality.md`/`motives.md`). The NEW datum: the ultrafilter spectrum
is the **same non-constructive object `nonstandard_analysis.md` located at LLPO** — so Stone duality has a
**calibrated boundary**: the finite/clopen Boolean side is ∅-axiom (`decide`/`Bool`), the full ultrafilter
Stone space sits on the same LLPO/choice strength. Be scrupulous which side is which.*

## The decomposition (C / L / Residue) — and where it splits

- **Construction `C` — the distinguishing-target `Bool`, and its `decide`-predicate algebra over `Raw`.**
  Stone duality's two sides share one construction: the two-valued distinguishing. A **Boolean algebra** is,
  in the calculus, the algebra of `Bool`-valued readings over the construction — exactly `topos.md`'s `Ω =
  Bool` with the membership/indicator reading `Object1 : Raw → (Raw → Bool)`
  (`FlatOntology.lean:43`, `Object1 r = fun s => decide (s = r)`), and the power-object predicate algebra
  `Type213 := (Fin n → Raw) → Bool` (`FlatOntology.lean:60`). A predicate `P : Raw → Bool` is exactly a
  "subobject"/algebra-element; the Boolean operations are the `decide`/`Bool` connectives (`∧`/`∨`/`¬` on
  `Bool`). And the **named abstract Boolean algebra is genuinely BUILT and ∅-axiom** — `Order/BooleanAlgebra`
  (25/0 PURE): the lattice+distributive+complemented axiom set supplied per-theorem (`propext`-free `rw`/`calc`
  on `Eq`), deriving idempotence, boundedness, **uniqueness of complement** (`cmpl_unique`), **double
  complement** (`cmpl_cmpl`), and **both De Morgan laws** (`de_morgan_inf`/`de_morgan_sup`), with the concrete
  witness `α = Bool` (`and/or/not/false/true`) discharged **by `decide`** (`bool_de_morgan_inf`, etc.). So `C`
  = the distinguishing-target `Bool` and its `decide`-predicate algebra, and the Boolean-algebra *structure*
  is not merely the predicate algebra in spirit — it is a built ∅-axiom object.

- **Reading `L` — the QUOTIENT/SPECTRUM reading: "a point = a consistent Bool-assignment to every
  element." This is where the object splits in two, exactly as `nonstandard_analysis.md` splits:**
  - **`L_decide` (the finite/clopen Boolean side) — INTERNAL, BUILT, PURE.** Each algebra-element IS a
    reading `Raw → Bool` (`Object1`, the predicate algebra). The clopen-↔-element correspondence is the
    duality at the level the calculus already has: a clopen set = a decidable predicate = an element of
    the `Bool`-valued algebra; evaluating an element AT a point = applying the reading. This half is the
    `decide`/`Bool` corner — the same Boolean pole `topos.md` proved is the PURE corner.
  - **`L_𝒰` (the ULTRAFILTER spectrum reading) — the EXTERIOR import. NOT built, and the calculus PROVES
    why.** A *point* of the Stone space `Spec(B)` is an **ultrafilter** on `B` = a maximal consistent
    assignment of `Bool` to *every* element, deciding for each `b` whether `b ∈ 𝒰` or `¬b ∈ 𝒰`. This is
    the **same non-principal ultrafilter** `nonstandard_analysis.md` located: the maximality that decides
    every subset, requiring Zorn/choice, with **no ∅-axiom witness** (the prime/maximal-ideal theorem for
    Boolean algebras is equivalent to the Boolean Prime Ideal theorem, BPI — a choice fragment). The
    reconstruction "the algebra ≃ the clopen sets of its spectrum of ultrafilters" is the
    points-from-readings move (`yoneda.md`/`tannakian_duality.md`/`motives.md`) — but at the *uncountable
    maximal* index, where it leaves the finite signature.

- **Residue, tagged `q = ±1` (`ResidueTag.lean`) — the spectrum reifies the points-from-readings residue.**
  - On `L_decide` (internal), the residue is the ordinary self-cover surplus: `Object1` is faithful
    (`object1_injective`, `FlatOntologyClosure.lean:47`, the Yoneda/faithfulness leg = "an element is
    determined by its Bool-readings") but **not total** (`object1_not_surjective`, `:61` — the predicates
    outside the image, the Cantor-unpointable surplus). `q=+1` where the reconstruction succeeds (faithful
    embedding `B ↪ clopen(Spec B)`), `q=−1` where it diagonalizes out.
  - The **break**: a *point* of the Stone space (an ultrafilter) is the points-from-readings residue
    **reified as an inhabited object** — exactly the move `nonstandard_analysis.md`'s `ε` performs. The
    calculus says the residue is *outside every view's image* (`object1_not_surjective`) — pointed at,
    never inhabited. The non-principal ultrafilter is precisely the device that *inhabits* it: it turns
    "the algebra of readings points at a maximal consistent valuation" (a `q=±1` pointing) into "this
    valuation IS a point of `Spec(B)`." The device that performs the reification is the same one
    (`𝒰`'s maximality), and its strength is the **same calibrated LLPO** `comparability_imp_llpo` measures.

## Re-seeing — ⟨C | L⟩ (the split shown explicitly)

```
   Bool-valued predicate algebra  =  ⟨ Raw | Object1 = decide(s=r) ⟩      (C = FlatOntology Ω=Bool, PURE)
   Boolean algebra B              =  the algebra of decidable predicates Raw → Bool  (topos.md Boolean pole)
   clopen ↔ algebra-element       =  evaluate-the-reading-at-a-point ⟺ the element  (the duality, L_decide)
   ─────────────────────────────────────────────────────────────────────────────────────────────────────
   FINITE / clopen Boolean side   =  ⟨ Bool-predicate algebra | L_decide ⟩   (INTERNAL: Object1, PURE)
   ─────────────────────────────────────────────────────────────────────────────────────────────────────
   Stone space Spec(B)            =  ⟨ B | L_𝒰 = ultrafilter spectrum ⟩       (EXTERIOR: 𝒰 = BPI/choice)
   a point of Spec(B)             =  an ULTRAFILTER = maximal consistent Bool-valuation  (= points-from-readings, REIFIED)
   B ≃ clopen(Spec B)             =  object = its readings reconstruction      (yoneda/tannakian/motives; q=±1)
   contravariant equivalence      =  Aut/character-style duality (clopen ↦ element, point ↦ ultrafilter)
   distributive lattice → spectral=  drop complement: Heyting/intuitionistic side  (topos.md PURE corner)
   Priestley (+ order)            =  the order-bit on the spectrum  (= the q=±1 direction/swap-bit, C-side)
   Residue(L_decide, C)           =  the un-pointable predicate, reached by none, q=±1  (object1_not_surjective)
```

The single move that locates the boundary: **the Bool-predicate algebra and the clopen↔element
correspondence are internal and PURE; the ultrafilter spectrum is the exterior import, imported for exactly
one job — totalization** (give every element a definite Bool-verdict at every point, so the
reconstruction's points become inhabited objects). That totalization is precisely the non-constructive act
`nonstandard_analysis.md` *measured at LLPO*, not flagged — the ultrafilter recurs verbatim.

## REVELATION — the Ω=Bool reading made a contravariant equivalence with its own spectrum; CALIBRATED at LLPO

Three findings, each grep-confirmed, that together pin the boundary at one primitive — and, crucially, the
SAME primitive `nonstandard_analysis.md` located.

### (1) A Boolean algebra = the algebra of Bool-valued readings (`Object1 = decide`) — INTERNAL, BUILT, PURE

`topos.md` proved (PURE) that `Ω = Bool` and `χ_A = Object1 : Raw → (Raw → Bool)` is the
characteristic/membership reading; subobjects/algebra-elements ARE decidable predicates `Raw → Bool`
(`Type213`, `FlatOntology.lean:60`). The Boolean side of Stone duality is therefore *already the calculus's
own Boolean pole*: a Boolean algebra = the `decide`/`Bool` predicate algebra, the connectives the
constructive `Bool` operations. And — sharper than `topos.md` recorded — the **named abstract Boolean algebra
is BUILT ∅-axiom**: `Order/BooleanAlgebra.lean` (25/0 PURE) derives uniqueness of complement, double
complement, and both De Morgan laws from the Huntington-style axioms by `propext`-free equational rewriting,
with the `Bool` witness `bool_de_morgan_inf`/`bool_cmpl_cmpl` discharged **by `decide`**. The
clopen-↔-element correspondence is the duality read at the level the calculus has: evaluating an
algebra-element at a point = applying the reading. This is the **`q=+1` PURE corner** `topos.md` identified
(Bool/decide PURE; classical `Prop` connectives DIRTY, `SemanticAtom` 11 pure / 23 dirty, all `[propext]`).
So the Boolean *algebra* side is built and ∅-axiom — as a named structure, not merely the predicate algebra.

### (2) The Stone space = the points-from-readings reconstruction — and the ultrafilter is the SAME calibrated exterior

The reconstruction "an object = its bundle of readings" is the calculus's deepest reflexive move:
`object1_injective` (`FlatOntologyClosure.lean:47`) is the faithfulness leg — *an element is determined by
its `Bool`-readings*, the Yoneda/`tannakian_duality.md`/`motives.md` "object = its realizations." Stone
duality `B ≃ clopen(Spec B)` is exactly this reconstruction made a contravariant equivalence. **But the
points of `Spec(B)` are ultrafilters**, and an ultrafilter does the one thing the internal predicate
algebra cannot: it **totalizes** — a maximal consistent assignment deciding *every* element. This is the
identical primitive `nonstandard_analysis.md` located, and the calculus has a *theorem* about its strength:

- **`comparability_imp_llpo`** (`RealComparabilityLLPO.lean:33`, PURE, scan 2/0): if any two corpus reals
  are comparable, then **LLPO** holds — the corpus is not constructively totally decidable.
- delegating to **`llpo_of_realDichotomy`** (`RealDichotomyLLPO.lean:525`, PURE, scan 31/0): the sign
  dichotomy already forces LLPO.

The ultrafilter's "decide `b ∈ 𝒰` or `¬b ∈ 𝒰` for every `b`" is **this very omniscient sign-decision
performed for every element at once** — the maximal, totalized version of the partial valuation the calculus
leaves as a pointing. So the Stone space is not an arbitrary construction the repo declined; it is the
**named non-constructive object** (`LPO`/`LLPO`, `Omniscience.lean:25/:35`) the calculus calibrates against
but never proves. The Boolean Prime Ideal theorem (= prime/maximal ideals exist) is choice-fragment strength
on exactly this omniscience ledger (the same ledger as `BolzanoWeierstrass.lpo_of_bw`). **This is the located
primitive: `𝒰`'s maximality = the totalization at LLPO-strength, no ∅-axiom witness.** Calibrated, not fatal.

### (3) The reification is the deeper break — the points-from-readings residue made an inhabited object

Even granting the Bool-algebra side, the *point* of the Stone space is the reconstruction-residue
**reified**: a definite inhabitant (the ultrafilter) realizing a maximal valuation. The calculus's residue
is reached-by-none — `object1_not_surjective` (`:61`) says the surplus is outside *every* view's image;
`cardinality.md`/`ordinals.md` make the rule explicit (the diagonal/`ω` is named by a finite signature,
never inhabited). The ultrafilter is precisely the device that inhabits it: it collapses "the algebra points
at a maximal valuation" (a pointing, `q=±1`) into "this is a point of `Spec(B)`." So the same primitive does
**both** forbidden jobs — totalize the valuation (finding 2) and reify the spectral point (finding 3) — the
exact two-job pattern `nonstandard_analysis.md` found for `𝒰` (totalize the order + reify `ε`). The
distributive-lattice generalization (spectral spaces) drops complement = drops to the **Heyting/constructive
side** (`topos.md`'s intuitionistic corner); Priestley duality re-adds an *order* bit on the spectrum =
the `q=±1` direction/swap-bit carried on `C`.

### Net revelation

Stone duality **splits at the spectrum reading**: `⟨Bool-predicate algebra | L_decide⟩` is internal and
PURE (the Boolean algebra of `Object1` readings, the clopen↔element duality at the decide level);
`⟨B | L_𝒰⟩` is the exterior import, and it is the **single primitive `𝒰`-maximality** — the SAME one
`nonstandard_analysis.md` located — that does two forbidden jobs at once: totalize the valuation (=
LLPO-strength, `comparability_imp_llpo`) and reify the spectral point (against `object1_not_surjective`). The
ultrafilter recurs *verbatim*: Stone's `Spec(B)` IS the points-from-readings reconstruction
(`yoneda`/`tannakian`/`motives`) carried to the maximal/uncountable index where it requires the calibrated
exterior. No-exterior survives as a claim under test (§5.4): the internal handle (the Bool-predicate algebra)
is built; the irreducible remainder (the ultrafilter spectrum) is *measured* at LLPO, not declared a wall.

## VALIDATE verdict — **LOCATED BOUNDARY** (calibrated at LLPO; the ultrafilter recurs verbatim)

This is NOT a clean EXTEND and NOT a fatal BREAK. It is a located, calibrated boundary — and its *novelty
over `topos.md`* is that it ties the Boolean pole's spectrum to the `nonstandard_analysis.md` ultrafilter.

- **Internal (EXTEND) part:** the **Boolean-algebra side** + the **clopen-↔-element duality** slot into the
  calculus with no new primitive — `C = Bool`-predicate algebra (`Object1 = decide`, `topos.md`'s Boolean
  pole), `L = L_decide`, `Residue` = the un-pointable predicate tagged `q=±1`. Built and PURE, and the
  **named abstract Boolean algebra IS built** (`Order/BooleanAlgebra` 25/0 — complement-uniqueness, De Morgan,
  `Bool` witness by `decide`), alongside `FlatOntology` 12/0, `FlatOntologyClosure` 7/0,
  `PredicateSelfEncoding` 7/0, `ResidueTag` 55/0.
- **BREAK part (the located primitive):** the **ultrafilter spectrum `Spec(B)`** — specifically the
  non-principal ultrafilter's *maximality* (deciding every element). It is the genuine exterior import, and
  it is **calibrated**: the totalization it performs (every point decides every element; the contravariant
  reconstruction's points inhabited) is *exactly* the LLPO/BPI-strength decision the calculus proves
  non-constructive (`comparability_imp_llpo` → `llpo_of_realDichotomy`). It has **no ∅-axiom witness**,
  sitting with `LPO`/`LLPO` as a `Prop` the corpus states and calibrates against. The named
  `Stone`/`Ultrafilter`/`Spec`/`Priestley`/`spectralSpace`/`clopen` objects are **ABSENT** (grep-confirmed
  empty — see Dropped/flagged). NOTE the named `BooleanAlgebra` is the exception: it **IS built** ∅-axiom
  (`Order/BooleanAlgebra` 25/0) — so the algebra side is named-and-built, only the *spectrum* side is absent.
- **Why this is the SAME boundary as `nonstandard_analysis.md` (the new datum):** the ultrafilter is not a
  new kind of exterior — it is the *already-charted* omniscience axis (LPO/LLPO/BPI), the identical
  primitive the hyperreal needed. Stone duality is the cleanest *order-theoretic* stress test because it
  tries to reify the points-from-readings residue as a topological space; the calculus's answer is that the
  reifying device (the ultrafilter) is precisely its named, measured non-constructive principle. The Boolean
  pole (`topos.md`) gains its spectrum, and the spectrum lands on the LLPO boundary (`nonstandard_analysis.md`).

## Verified Lean anchors (file:line:theorem) — all grep-confirmed; scans from repo root

**The Boolean-algebra side — NAMED structure BUILT (`Order/BooleanAlgebra` 25/0 PURE):**
- `lean/E213/Lib/Math/Order/BooleanAlgebra.lean:80` `cmpl_unique` (uniqueness of complement), `:112`
  `cmpl_cmpl` (double complement), `:133` `de_morgan_inf`, `:185` `de_morgan_sup` (both De Morgan laws),
  `:31` `idem_inf`/`:40` `idem_sup`, `:51` `inf_bot`/`:63` `sup_top`; concrete witness `:278`–`:291`
  `bool_*` axioms by `decide`, `:295` `bool_de_morgan_inf`, `:305` `bool_de_morgan_sup`, `:314`
  `bool_cmpl_cmpl` (the `α = Bool` Boolean algebra, axiom-clean). Scan **25 pure / 0 dirty**.

**The `Ω=Bool` reading / predicate algebra / reconstruction (`FlatOntology` 12/0, `FlatOntologyClosure` 7/0 PURE):**
- `lean/E213/Lens/Foundations/FlatOntology.lean:43` `Object1` (`= fun s => decide (s = r)`, the membership
  reading = a Boolean-algebra element/clopen), `:46` `Object1_self`, `:60` `Type213 := (Fin n → Raw) → Bool`
  (the predicate algebra = the Boolean algebra of decidable readings).
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:47` `object1_injective` (faithful: an element is
  determined by its Bool-readings — the Yoneda/`tannakian`/`motives` reconstruction leg), `:61`
  `object1_not_surjective` (the un-pointable residue, Cantor), `:69` `self_covering_closure`.
- `lean/E213/Lens/Foundations/PredicateSelfEncoding.lean:71` `predicateToRaw`, `:91`
  `predicate_self_encoding_closure` (the power-object/predicate-algebra round-trip; scan 7/0 PURE).

**The Bool-PURE vs classical-Prop split (the Boolean pole is PURE; going classical costs `propext`):**
- `lean/E213/Lens/Foundations/SemanticAtom.lean:108` `universalMorphism`, `:412` `raw_initial` (the
  read-op / initiality = the reconstruction's unique arrow). Scan **11 pure / 23 dirty** — the dirty are
  the classical `Prop` connectives (`canonicalTruthMap`, `propAsDistinguishing{,Iff}`, `propXor_comm`, …),
  all `[propext]`; the `Bool`/`decide` Boolean pole is PURE.

**The ultrafilter spectrum's totalization = LLPO (the calibrated exterior — the SAME as nonstandard_analysis.md):**
- `lean/E213/Lib/Math/Logic/RealComparabilityLLPO.lean:33` `comparability_imp_llpo` (PURE, scan 2/0):
  total comparability ⟹ LLPO — not constructively totally decidable.
- `lean/E213/Lib/Math/Logic/RealDichotomyLLPO.lean:525` `llpo_of_realDichotomy` (PURE, scan 31/0): the
  sign dichotomy ⟹ LLPO (the omniscient decision the ultrafilter performs for every element).
- `lean/E213/Lib/Math/Logic/Omniscience.lean:25` `LPO`, `:35` `LLPO` (the omniscience ledger the
  ultrafilter/BPI sits on; scan 8/0 PURE).
- `lean/E213/Lib/Math/NumberSystems/Hyper/Hyper213.lean:43` `Hyper213`, `:46` `cofiniteEquiv`, `:67`
  `constHyper`, `:70` `const_equiv_iff` (the cofinite-filter internal horn — the filter the residue admits,
  one step below the ultrafilter the spectrum needs; scan 7/0 PURE; `nonstandard_analysis.md`'s anchor).

**The residue (reached-by-none — what the spectrum reifies) and the q=±1 tag:**
- `lean/E213/Lens/Cardinality/Cantor.lean:36` `cantor_raw_bool`, `:23` `cantor_general` (the diagonal
  driving `object1_not_surjective`).
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:73` `ResidueTag` (inductive escape|converge), `:86`
  `multiplier_unimodular`, `:133` `escape_residue_outside`, `:160` `converge_residue_fixed`, `:180`
  `golden_is_converge`, `:228` `residue_tag_two_poles` (scan 55/0 PURE).
- `lean/E213/Lib/Math/Order/GaloisConnection.lean:104` `clo`, `:107` `clo_extensive`, `:126`
  `clo_idempotent` (the closure operator — the ideal↦its-closed-set, `V⊣I`-style adjoint that the
  distributive/spectral generalization's ideal-variety machinery would instantiate; same `f**=clo` family).

**Scan tallies (`python3 tools/scan_axioms.py <module>`, from repo root):**
`Order.BooleanAlgebra` 25/0 · `FlatOntology` 12/0 · `FlatOntologyClosure` 7/0 · `PredicateSelfEncoding` 7/0 ·
`ResidueTag` 55/0 · `RealComparabilityLLPO` 2/0 · `RealDichotomyLLPO` 31/0 · `Omniscience` 8/0 ·
`Hyper213` 7/0 · `SemanticAtom` 11/23 (the 23 dirty = the classical `Prop` connectives, all `[propext]`; the Bool/decide
Boolean pole PURE). All cited *theorems* on the internal side are 0-DIRTY.

## Dropped / flagged

- **`BooleanAlgebra` — found BUILT, correcting the prediction.** The thesis predicted the named
  `BooleanAlgebra` object likely ABSENT; grep found it **present and ∅-axiom** (`Order/BooleanAlgebra.lean`,
  25/0 PURE — complement-uniqueness, double complement, both De Morgan laws, `Bool` witness by `decide`).
  This *strengthens* the verdict: the algebra side is not just "the predicate algebra in spirit" but a named
  built structure; only the *spectrum* side is the exterior.
- **Named `Stone` / `DistributiveLattice` / `Ultrafilter` / `Spec` / `Priestley` / `spectralSpace` /
  `clopen` / `primeIdeal` objects — ABSENT (grep-confirmed, predicted not-built).** Grep over `lean/E213`
  for `stone|priestley|spectralspace|distributivelattice|ultrafilter|prime_ideal|primeideal|clopen` returns
  **zero declarations** (the only `ultrafilter` hits are `Hyper213.lean` *docstrings* naming it the rejected
  primitive; the `lattice` hits are the *prime-exponent* lattice `VpMul`/`ExpVector`, a different object; the
  `maximal ideal` hits are `Padic/NuEscape`'s `pℤ_p`, the p-adic valuation ideal, not a Boolean-algebra
  spectrum; the `spectrum` hits are the Markov/Lagrange approximation spectrum). NOT asserted as built —
  the predicted absence confirmed for the spectrum side.
- **The Stone space `Spec(B)` / its topology / compactness-of-the-spectrum — ABSENT, and provably the
  LLPO/BPI exterior.** No `Spec`/spectrum-of-a-Boolean-algebra object exists. Its points (ultrafilters)
  require BPI = a choice fragment on the omniscience ledger (`comparability_imp_llpo`), with no ∅-axiom
  witness. The compactness of the Stone space is itself equivalent to BPI — the same `q=−1` totalization.
  Flagged as the open object the boundary forbids (the analogue of `nonstandard_analysis.md`'s absent
  transfer/Łoś, `topos.md`'s absent named topos object).
- **The contravariant equivalence `BoolAlg ≃ Stone` as a NAMED equivalence — CONCEPTUAL.** The
  reconstruction content (`object1_injective` faithfulness, the points-from-readings move) is built and
  PURE; the named functorial equivalence is absent because `Stone`/`Spec` are absent. The clopen↔element
  half is internal (`L_decide`); the full equivalence needs the ultrafilter side.
- **No verified buildable witness proposed.** No ∅-axiom witness for the Stone-space side is buildable
  (it is the LLPO/BPI exterior — proving it would require a choice fragment the discipline forbids). No
  decide-witness is proposed; the boundary is correctly located on the non-constructive side, not patched.
- **No claim that the Bool-predicate algebra IS a Boolean algebra in the named sense.** It is the
  `decide`/`Bool` predicate algebra (`topos.md`'s Boolean pole); asserting it bundles a `BooleanAlgebra`
  structure with complement/De-Morgan as a named object would overstate — the operations are present as the
  `Bool` connectives, the bundled structure is not built.
```
