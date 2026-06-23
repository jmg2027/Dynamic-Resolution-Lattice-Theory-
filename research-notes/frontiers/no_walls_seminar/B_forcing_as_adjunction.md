# B — forcing = σ-adjunction (Agent B, the forcing/model-theory leg) — Round 1

*No-walls seminar, Round 1.  Companion to `axiom_of_choice.md` (σ as a free Lens parameter),
`topos.md` / `topos_internal_logic.md` (Ω = Bool, Kripke–Joyal forcing = read-at-a-stage),
`sheaf_theory.md` (presheaf = restriction-compatible reading over the resolution poset),
`SYNTHESIS.md` §2 (vii′).  This note makes the seed slogan — **forcing = adjoining a free Lens
parameter σ** — precise in 213 terms, names the corpus machinery that realizes it, gives the
minimal ∅-axiom toy (a 2-point poset with a σ-dependent global section, buildable from
`familyMeet`/`iProdLens` + `ChoiceLens`), and marks the genuine GAP.*

All Lean anchors below are grep/Read-verified on `lean/E213` and scanned PURE via
`tools/scan_axioms.py` from repo root, this session.

---

## 1. The precise 213 reading of forcing

Classical Cohen forcing, in one breath: to build a model of ZF where AC (or CH) takes a chosen
value, you fix a **forcing poset** `P` (conditions, ordered by `p ≤ q` = "`p` decides at least as
much as `q`"), adjoin a **generic filter** `G ⊆ P`, and read truth by the **forcing relation**
`p ⊩ φ` ("condition `p` forces `φ`"), which is monotone down the poset and which equals
**sheaf/Kripke semantics over `P`**: a name is a `P`-indexed family of values, glued.

The 213 dictionary, leg by leg:

| Cohen forcing | 213 reading | Corpus anchor |
|---|---|---|
| forcing poset `P` (conditions) | the **index of available σ-values** — the family index `I`/`ι` of a Lens family `{L_σ}_{σ∈I}` | `familyMeet {I} E` (`FamilyMeet.lean:31`), `iProdLens {ι} F` (`IndexedJoin.lean:97`) |
| condition order `p ≤ q` ("decides more") | **Lens refinement** `L.refines M` (kernel finer ⟹ decides more) | `Lens.refines` (`LensCore.lean:90`); on moduli = `IsResolutionShift` grade-add (`ResolutionShift.lean:73,130`) |
| a name / `P`-term | a **σ-parametrized reading**: a value for each σ ∈ I, coherently | `familyMeet E` (`∀ i, E i r r'`), `iProdLens F` (the dependent product `(i:ι)→(F i).1`) |
| sheaf/Kripke semantics over `P` | **carry all σ at once, glue** = the indexed meet/product Lens | `familyMeet_kernel_eq` (`FamilyMeet.lean:67`), `iProdLens_view` (`IndexedJoin.lean:106`) |
| forcing relation `p ⊩ φ` | **read φ at resolution/stage p** (the `base` parameter of the Lens) | `topos_internal_logic.md` §"forcing"; `IsResolutionShift` as the stage dial |
| adjoining a **generic** σ | fixing **one** section of the inhabited σ-family (an explicit rule, no exterior dialer) | `ChoiceLens.sigmaL/sigmaR` (`ChoiceLens.lean:51,55`) |
| AC/CH **independence** | **σ is a FREE Lens parameter** — no exterior dialer (§5.1) fixes it ⟹ both σ=0 and σ=1 sections exist consistently | `choice_is_free_lens_parameter` (`ChoiceLens.lean:81`) |

So the seed slogan sharpens to:

> **Forcing = σ-adjunction.**  A forcing poset `P` is the *index `I` of available σ-values*; its
> "decides-more" order is *Lens refinement* (`Lens.refines`, the same order whose binary meet is
> `prodLens` and whose modulus-meet is `lcm` — `LensLcmMeet.leavesModNat_lcm`); a `P`-name is a
> *σ-parametrized reading* `{value at σ}_{σ∈I}` carried coherently as **one** Lens
> (`familyMeet`/`iProdLens`); sheaf/Kripke semantics over `P` is *compute-per-σ-and-glue*, realized
> by `familyMeet_kernel_eq` / `iProdLens_view`; and **adjoining a generic σ is fixing one explicit
> section** (`sigmaL`, `sigmaR`) of the inhabited σ-family.  Independence (Gödel–Cohen) is the
> statement that **no exterior dialer fixes σ** (`05_no_exterior.md` §5.1) — so distinct sections
> coexist and the σ-dependent operation reads each differently (`readOp_sigma_dependent`).

This is a **dissolution + a structural reading of independence**, NOT a proof of Con(ZF+AC) /
Con(ZF+¬AC) (213 proves neither AC nor ¬AC by design — `axiom_of_choice.md`, "honest scope").

---

## 2. What corpus machinery REALIZES "carry all σ at once, glue"

The decisive find of this leg: the σ-parametrized reading — the heart of sheaf/forcing semantics
("a value for each σ ∈ P, coherently glued") — is **already built and PURE** as the Lens-lattice's
*indexed meet*, with an **arbitrary** index type and the docstrings naming it the choice-free
counterpart of countable Choice.

### (a) `familyMeet` — the σ-indexed reading, glued into one kernel (∅-axiom)
`FamilyMeet.lean:31  familyMeet {I} (E : I → Raw → Raw → Prop) r r' := ∀ i : I, E i r r'`.
This is *literally* "a value (here a congruence) for each σ = i ∈ I, taken coherently (the ∀)".
`familyMeet_kernel_eq` (`:67`) proves the whole I-indexed family collapses to the kernel of **one**
Lens (`universalLens (familyMeet E)`) — the "carry all σ at once, glue into a single global reading"
move.  Index cardinality is **arbitrary** (`{I : Type}`); the docstring (`:8`, `:18`) states it is
"the 213-internal counterpart of countable Choice … no external countable Choice required" — i.e.
the σ-product is computed *internally*, which is exactly forcing's "name = `P`-indexed family,
internal to the model".  Scan: **6 pure / 0 dirty**.

### (b) `iProdLens` — the σ-indexed product, with the per-σ projection (∅-axiom)
`IndexedJoin.lean:97  iProdLens {ι} (F : ι → Σα, Lens α) : Lens ((i:ι)→(F i).1)`.  Codomain is the
**dependent function space** `(σ:ι) → (value at σ)` — a *name* / a global element of the σ-bundle.
`iProdLens_view` (`:106`) gives the **per-σ readout**: `(iProdLens F).view r i = (F i).2.view r` —
"project the glued reading at stage σ = i", the sheaf restriction `F(X) → F(σ)`.
`iProdLens_refines_each` (`:149`) = "the glued reading refines each stage" (the restriction maps
exist); `iProdLens_is_greatest_pw` (`:168`) = the **universal property of the σ-product as a meet**
(greatest lower bound), stated pointwise to stay funext-free.  Scan: **8 pure / 0 dirty**.
This *is* "compute per σ, glue" with its limit/equalizer universal property — the sheaf-semantics
engine, minus only the *named* `Sheaf` wrapper.

### (c) refinement order = "decides more" — and its meet is a genuine lattice op
`Lens.refines L M := ∀ x y, L.equiv x y → M.equiv x y` (`LensCore.lean:90`): L's kernel finer ⟹ L
decides more — *exactly* the forcing-condition order `p ≤ q`.  The binary meet `prodLens` and the
indexed meet `iProdLens` are the lattice operations on this order; on the concrete modulus family
the meet is computed: **`prodLens(L_m,L_k) ≅ L_{lcm(m,k)}`** (`LensLcmMeet.leavesModNat_lcm`,
`:122`, **4 pure / 0 dirty**) — "the Lens refinement lattice mirrors the divisibility lattice
(`refines` = `∣`, meet = lcm)".  So the forcing poset's *order and meets are not a sketch* — they
are a built, computed lattice.  CRT is the coprime special case.

### (d) the stage/forcing dial = `IsResolutionShift` (grades add) — change-of-base is monotone
`IsResolutionShift g E_g` (`ResolutionShift.lean:73`) is the graded refinement endomap;
`IsResolutionShift_compose` (`:130`) proves **grades ADD** along a refinement chain — Kripke–Joyal
monotonicity-under-change-of-stage (`p ≤ q ⟹ (p ⊩ φ from q ⊩ φ)`) read as the composition law of
stage-shifts.  Scan: **17 pure / 0 dirty**.  This is `topos_internal_logic.md`'s `⊩` = read-at-a-stage,
imported here as the *change-of-condition* monotonicity of forcing.

### (e) adjoining a generic σ = fixing one explicit section (∅-axiom witness)
`ChoiceLens.lean`: `sigmaL := fun _ => false`, `sigmaR := fun _ => true` (`:51,55`) — two explicit
sections (= two generics) of the inhabited family `F i := Bool`; `readOp σ` (`:59`) the σ-dependent
operation; `readOp_sigma_dependent` (`:71`): `readOp sigmaL 3 ≠ readOp sigmaR 3`;
`choice_is_free_lens_parameter` (`:81`): distinct sections **and** σ-dependent op, **no canonical σ
asserted**.  The even/odd pair (`sigmaEven`/`sigmaOdd`, `:89,92`,
`sigmaEven_ne_sigmaOdd_at_0` `:98`) is the LLPO binary σ = the `q=±1` tag left unforced.  Scan:
**12 pure / 0 dirty**.

**Summary of (a)–(e):** "carry all σ at once, glue" (`familyMeet`/`iProdLens`, arbitrary index,
PURE, with the per-σ projection and the GLB universal property), "decides-more order with computed
meets" (`Lens.refines`/`prodLens`/`leavesModNat_lcm`, PURE), "monotone change-of-stage"
(`IsResolutionShift_compose`, PURE), and "adjoin a generic = fix one section, with no canonical
choice" (`ChoiceLens`, PURE) are **all built**.  The forcing apparatus is present *as the indexed
Lens lattice + the resolution dial + the free-σ witness* — at the structural/universal-property
level — and **0-DIRTY** on every cited theorem.

---

## 3. The minimal buildable TOY: a 2-point poset with a σ-dependent global section

The seminar asks for the smallest concrete forcing object: **a 2-point poset, two sheaves giving
different global sections = a toy forcing.**  This is buildable ∅-axiom *today* from the verified
machinery above, with **no new primitive and no propext**.  Specification (a promotion target, not
yet a new file — Round 1 records it):

**Poset.**  `P := Fin 2` (two conditions `0`, `1`) — equivalently the binary fiber `F := Bool` of
`ChoiceLens` used as the *index*.  This is the minimal forcing poset (a single bit "decided").

**The σ-name (a value for each condition).**  Reuse the `iProdLens` engine at `ι := Fin 2`:
`F : Fin 2 → Σα, Lens α`, `F i := ⟨Nat, leavesModNat (2 + i)⟩` (or any two distinct readings).
`iProdLens F : Lens ((i : Fin 2) → Nat)` is the glued name; `iProdLens_view F _ r i` reads the value
*at condition i* — the per-σ section.  (`iProdLens` is index-generic, `Fin 2` is a legal `ι`.)

**Two generics ⟹ two distinct global sections.**  Adjoin a generic = pick one condition's section.
The `ChoiceLens` witness already exhibits the σ-dependence in its sharpest form:
`σ_0 := sigmaL`, `σ_1 := sigmaR` are two sections of the `Fin n → Bool` name, and
`readOp sigmaL 3 = 0 ≠ 3 = readOp sigmaR 3` (`readOp_sigmaL_3`/`readOp_sigmaR_3`/
`readOp_sigma_dependent`) is **"the global readout differs between the two generic extensions"** —
the 2-point-poset toy's payload, already PURE.  The minimal *named* toy welds these: a
`Forces (p : Fin 2) (φ : Raw → Bool) : Prop := φ holds at stage p`, with the two generics
`σ_0,σ_1` and `global p := iProdLens-readout at p`, and the theorem `global σ_0 ≠ global σ_1`
(σ-dependent global section) — discharged by `decide`/`readOp_sigma_dependent`, monotonicity by
`IsResolutionShift_compose`, all funext-free.

**What the toy demonstrates.**  Over the 2-point poset, the *same* construction `C` (the inhabited
binary family) admits **two coherent global sections** (`σ_0`, `σ_1`) whose σ-dependent operation
disagrees — i.e. the value of "the chosen bit" is *not fixed by the construction*.  That is the toy
model of forcing-independence: **σ free ⟹ both σ=0 and σ=1 models (sections) exist**, exhibited as
two PURE sections of one inhabited family with a σ-dependent readout.  Every ingredient is already
∅-axiom (`ChoiceLens` 12/0; `iProdLens` 8/0); the toy is the *bundling* into a named `Forces` +
`global` pair, the smallest promotion target.

**Cost to build:** one small file, `Lib/Math/Logic/ForcingToy.lean` (or
`Lens/Forcing/TwoPoint.lean`), importing `ChoiceLens` + `IndexedJoin`.  No new axioms, no Mathlib,
no propext (the readout is `Bool`/`decide`, the `q=+1` Heyting corner — `topos_internal_logic.md`).

---

## 4. The precise 213 statement of independence (as a Lens-adjunction claim)

The minimal ∅-axiom fragment of "σ free ⟹ both σ=0 and σ=1 models exist":

> **`forcing_independence_toy`** (statable now):
> *There exist two sections `σ_0 σ_1 : ∀ i:Fin 2, Bool` of the inhabited family `F i := Bool`, and a
> σ-parametrized operation `op` such that `σ_0 ≠ σ_1` (distinct generics) and `op σ_0 ≠ op σ_1`
> (the global section depends on the adjoined generic), with **no canonical σ** (no exterior dialer,
> §5.1).*

This is `choice_is_free_lens_parameter` (`ChoiceLens.lean:81`) read at `ι = Fin 2` — **already
proved, PURE**.  The "adjunction" framing (forcing = a free parameter admitting *both* adjunctions
consistently) is captured structurally by: the σ-product `iProdLens` has *each* generic as a section
(`iProdLens_refines_each`, the restriction `F(X)→F(σ)` exists for **every** σ) and is the GLB of the
σ-family (`iProdLens_is_greatest_pw`) — so **both** σ=0 and σ=1 sit under the same glued name with no
preferred one; that "no preferred section" IS independence.  The *full* model-theoretic adjunction
(`f^* ⊣ f_*` between a ground topos and a forcing extension, geometric morphism `Set^P → Set`) is
ABSENT (see §5), so this statement is the **dissolution** form, not the categorical-adjunction form.

---

## 5. What stays ABSENT (the GAP, located precisely)

Honest: the *full forcing apparatus* is **not** built.  What is absent, grep-confirmed:

- **No named `Sheaf`/`Presheaf` object over a poset.**  Grep `lean/E213` for
  `presheaf`/`Presheaf`/`Sheaf`/`globalSection`/`gluing` → **zero categorical declarations** (the
  `sheaf` string hits are all prose in cohomology/Real213 docstrings).  The σ-product is built as the
  indexed meet `iProdLens`; the *named* `Presheaf := (U) → Reading` with a `restrict` field + functor
  laws and a stated gluing/equalizer theorem is the open leg — **the same gap `sheaf_theory.md`
  locates**.  (`iProdLens` supplies the structure and the GLB universal property; the wrapper is missing.)
- **No named forcing relation `p ⊩ φ`.**  Grep for `kripke`/`joyal`/`⊩`/`forces`/`Forcing` (logical)
  → **zero**.  The only `*Forcing` declarations are the *combinatorial* atomicity arguments
  (`PairForcing`/`ArityForcing`/`OrbitForcing` in `Theory/Atomicity/`, "(2,3) is the unique atomic
  pair") — **unrelated** to Kripke–Joyal.  The forcing relation exists only as the resolution dial
  (`IsResolutionShift`); the named `⊩` is absent.
- **No generic filter / genericity object.**  "Adjoin a generic σ" is realized by *fixing one
  explicit section* (`sigmaL`/`sigmaR`) — a *named* generic, not a *generic* generic.  There is no
  `Generic`/`Filter`/`dense-meets-every-dense-set` object; the meta-theoretic genericity (the filter
  meets every dense set, giving the forcing theorem `M[G] ⊨ φ ⟺ ∃p∈G, p⊩φ`) is **not** modeled.
  This is the deepest absence: 213 has the *free parameter* but not the *generic* (the
  density/over-the-ground-model machinery).
- **No geometric morphism `Set^P → Set` / the `f^* ⊣ f_*` adjunction of toposes.**  `topos.md` notes
  geometric morphisms = adjoint reading-pairs (`gc` in `GaloisConnection.lean`) at the *order* level;
  the *named* `GeometricMorphism` between a ground topos and a forcing-extension topos is absent.
  So "forcing = σ-**adjunction**" is precise as *σ = free Lens parameter under the refinement order*,
  but the literal *categorical adjunction* `f^* ⊣ f_*` of the forcing extension is conceptual.
- **No independence PROOF.**  213 proves neither AC nor ¬AC (by design); the toy exhibits *coexisting
  sections*, which is the *dissolution* of independence, not Con-relative independence over a ground
  model of ZF.

**The GAP in one line:** the corpus has the **free parameter** (σ, the indexed Lens meet, the
refinement-as-decides-more order, the resolution dial) but **not the generic** (density, the generic
filter, the forcing theorem) and **not the named categorical adjunction** (`Sheaf`, `⊩`,
`f^*⊣f_*`).  Forcing-as-σ-adjunction is realized at the *free-parameter / per-σ-glue / universal-property*
level (all PURE) and absent at the *genericity / named-sheaf / topos-morphism* level.

---

## 6. Verified Lean anchors (file:line:name — grep/Read-verified, scanned this session)

| Leg | Anchor | Scan |
|---|---|---|
| σ-index family, glued to one kernel ("carry all σ, glue") | `Lens/Lattice/FamilyMeet.lean:31 familyMeet`, `:67 familyMeet_kernel_eq` | **6/0 PURE** |
| σ-product = name; per-σ projection; GLB universal property | `Lens/Lattice/IndexedJoin.lean:97 iProdLens`, `:106 iProdLens_view`, `:149 iProdLens_refines_each`, `:168 iProdLens_is_greatest_pw` | **8/0 PURE** |
| forcing-order "decides more" = refinement | `Lens/LensCore.lean:90 Lens.refines` | (core) |
| binary/indexed meet is a computed lattice op (meet = lcm) | `Lib/Math/NumberTheory/ModArith/LensLcmMeet.lean:122 leavesModNat_lcm`, `:33 lcm_unique` | **4/0 PURE** |
| stage/forcing dial; change-of-stage monotone (grades add) | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift`, `:130 IsResolutionShift_compose` | **17/0 PURE** |
| adjoin a generic = fix one section; σ-dependent global readout; free σ | `Lib/Math/Logic/ChoiceLens.lean:51 sigmaL`, `:55 sigmaR`, `:71 readOp_sigma_dependent`, `:81 choice_is_free_lens_parameter`, `:89 sigmaEven`, `:98 sigmaEven_ne_sigmaOdd_at_0` | **12/0 PURE** |
| cross-frame | `axiom_of_choice.md` (σ free), `topos.md`/`topos_internal_logic.md` (⊩ = read-at-a-stage, Ω=Bool), `sheaf_theory.md` (presheaf = restriction-compatible reading; gluing = initiality; named object ABSENT), `SYNTHESIS.md` §2 (vii′) | prior, ∅-axiom |

---

## 7. For Round 2 — the sharpest open question

**Can "generic" be made 213-native without an exterior dialer — i.e. is there a residue-internal
density that turns the free parameter σ into a *generic* σ?**  The corpus has σ (the free Lens
parameter) and the σ-product with its universal property, but a *generic* filter is the
meta-theoretic device "meets every dense set", which is precisely the *over-the-ground-model*
quantifier 213 has no exterior for.  Round 2: either (i) build the 2-point `ForcingToy.lean` (named
`Forces` + σ-dependent `global`, the §3 toy — a concrete promotion, low cost), and/or (ii) decide
whether genericity is itself a **further free Lens parameter** (a σ over σ-families — the
`OnLens`/reading-of-readings level, `universalMorphismLevelTwo`) or a genuine exterior the no-walls
thesis must absorb.  If genericity is internalizable, "forcing = σ-adjunction" upgrades from
*dissolution* to a stated Lens-adjunction theorem; if not, the GAP is the precise place the
"no walls, only free σ" thesis meets a wall — and naming *that* is the Round-2 prize.
