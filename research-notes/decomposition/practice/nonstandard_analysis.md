# Decomposition: non-standard analysis / the hyperreals ℝ* (a STRESS TEST — located boundary)

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`), run as a
deliberate stress test for the no-exterior axiom (`seed/AXIOM/05_no_exterior.md` §5.1). The object: the
ultrapower `ℝ* = ℝ^ℕ / 𝒰` for a non-principal ultrafilter `𝒰`, infinitesimals, the transfer principle,
the standard-part map `st(·)`, Łoś's theorem. The crux question: **is the hyperreal construction a
genuine EXTERIOR import that BREAKS §5.1, or is it internalizable as a pointing/modulus?** The honest
verdict is a LOCATED BOUNDARY that splits cleanly down the middle — the same shape as `knots.md` and
`model_theory.md`'s missing leg — and the boundary is **calibrated** (LPO/LLPO-named), not fatal.*

## The decomposition (C / L / Residue) — and where it splits

- **Construction `C` — the raw sequence `Nat → Raw`, NO modulus.** A hyperreal is, before any quotient,
  a sequence of distinguishables. The repo builds *exactly this*: `Hyper213 := Nat → Raw`
  (`Hyper213.lean:43`). This is `continued_fractions.md`/`padic.md`'s "a number is an approximant
  sequence" `C` with the modulus **dropped** — the file's own framing: "sequences only — *without* a
  Cauchy modulus." So `C` is internal and the construction-history is the bare distinguishing iterated
  over `Nat`. An **infinitesimal** is the construction `(1/n)ₙ` — the sequence whose terms shrink — read
  *as an object* rather than as a pointing. A constant sequence `constHyper r` (`:67`) embeds each
  standard `Raw`; `const_equiv_iff` (`:70`) makes the embedding faithful (the `*ℝ ⊇ ℝ` inclusion).

- **Reading `L` — the QUOTIENT reading on sequences. This is where the object splits in two:**
  - **`L_cofin` (cofinite / "eventually equal") — INTERNAL, BUILT, PURE.** `cofiniteEquiv xs ys :=
    ∃ N, ∀ n ≥ N, xs n = ys n` (`Hyper213.lean:46`) — agree from some `N` onward. This is a genuine
    equivalence (`cofinite_refl/symm/trans`, `:49/:52/:57`), strictly *looser* than Cauchy-equivalence
    (`ClassicalAnalysisCompletenessAsLens.lean:54` `cauchyEquiv`), and the file states the relation
    precisely: Cofinite-equal sequences land in one class — "eventually indistinguishable." This is a
    reading whose **kernel is the cofinite filter** — the *Fréchet filter* of cofinite sets.
  - **`L_𝒰` (the ULTRAFILTER reading) — the EXTERIOR import. NOT built, and the calculus PROVES why.**
    The classical hyperreal demands *more* than cofinite: a **non-principal ultrafilter** `𝒰 ⊇` the
    cofinite filter that decides, for *every* set `S ⊆ ℕ`, whether `S ∈ 𝒰` or `Sᶜ ∈ 𝒰` — the
    maximality that the cofinite filter lacks. This is the device that makes the quotient a **total
    ordered field** and lets **Łoś's theorem** assign every first-order statement a definite truth value
    "on a `𝒰`-large set." `𝒰` requires Zorn / the axiom of choice and has **no ∅-axiom witness**.

- **Residue, tagged `q = ±1` — but with a TWIST: the hyperreal tries to REIFY the residue.**
  - On `L_cofin` (internal), the residue is the ordinary completion residue: the *limit* the sequence
    points at, reached by none — the `object1_not_surjective` / `distinguishing_always_leaves_residue`
    signature (`FlatOntologyClosure.lean:61/:69`). `q = +1` convergent pointing (the sequence has a
    fixed-point limit), `q = −1` escaping (oscillating, no limit). Standard fare.
  - The **break**: an infinitesimal `ε` "smaller than every `1/n` but `≠ 0`" is the residue-doctrine's
    *reached-by-none* boundary **reified as an inhabited object**. The calculus says the residue is
    *outside every view's image* (`object1_not_surjective`) — pointed at, never inhabited
    (`cardinality.md`: "naming it does not inhabit it"; `ordinals.md` caps at `ω`, named by its finite
    generator, never inhabited). The classical hyperreal `ε` is the residue *given a definite value
    inside the field* — exactly the move "Limit/infinity deified" (CLAUDE.md) forbids. The device that
    performs the reification is the ultrafilter: `𝒰` is what turns "the sequence `(1/n)` points below
    everything" (a `q=±1` pointing) into "`[(1/n)]` IS a number with a definite sign and order-position."

## Re-seeing — ⟨C | L⟩ (the split shown explicitly)

```
   hyperreal sequence       =  ⟨ Nat → Raw (no modulus) | — ⟩            (C = Hyper213, BUILT, PURE)
   infinitesimal (1/n)ₙ     =  the shrinking construction, read as object (residue reified — the break)
   ℝ ⊂ ℝ*  (constants)      =  constHyper + const_equiv_iff             (faithful embedding, BUILT)
   ─────────────────────────────────────────────────────────────────────────────────────────
   cofinite quotient ℝ^ℕ/Fréchet  =  ⟨ Hyper213 | L_cofin ⟩            (INTERNAL: cofiniteEquiv, PURE)
   ─────────────────────────────────────────────────────────────────────────────────────────
   ultrafilter quotient ℝ^ℕ/𝒰     =  ⟨ Hyper213 | L_𝒰 ⟩               (EXTERIOR: 𝒰 = AC, NO witness)
   transfer / Łoś                  =  L_𝒰 makes every statement decided  (ABSENT; needs 𝒰's maximality)
   total order  [x] < [y]          =  L_𝒰 totalizes the comparison      (= comparability ⟹ LLPO, BUILT-as-calibration)
   standard part  st(·)            =  the residue-discarding reading: project halo → its real shadow
   Residue(L_cofin, C)             =  the limit, reached by none, q=±1   (object1_not_surjective)
```

The single move that locates the boundary: **the cofinite filter is internal; the ultrafilter is the
exterior import, and it is imported for exactly one job — totalization** (give every `S ⊆ ℕ` a verdict, so
every comparison and every first-order statement gets a definite truth value). That totalization is
precisely the non-constructive act the calculus has *measured*, not just flagged.

## Revelation — LOCATED BOUNDARY (the ultrafilter is the calibrated exterior; the sequence is internal)

Three findings, each grep-confirmed, that together pin the boundary at one primitive.

### (1) The sequence + cofinite quotient is INTERNAL and BUILT (the INTERNAL horn, partly cashed)

`Hyper213` (`:43`, `Nat → Raw`) + `cofiniteEquiv` (`:46`) is a ∅-axiom object (scan 7/0 PURE). The
repo's own design note states the position exactly: *"Hyper213 = the cofinite quotient of sequences —
weaker than ZFC's free ultrafilter (NSA) but framework-internal. Most exotic number systems
(hyperreals, surreals, ...) are quotients of sequences or tree structures — naturally captured. Only
arbitrary subsets (power sets) are rejected."* So the **infinitesimal-as-sequence is genuinely
internal** — it is the `padic.md`/`continued_fractions.md` "number = approximant sequence + modulus"
shape with the modulus dropped, and it slots into the calculus with no new primitive. The internal horn
(b) of the test is **confirmed for the sequence layer**: an infinitesimal IS a modulus/pointing, the
ultrapower IS the sequence space.

### (2) The ULTRAFILTER is the exterior import — and the calculus proves WHY it cannot be internal

The ultrafilter does one thing the cofinite filter cannot: it **totalizes**. A non-principal `𝒰` decides
every `S ⊆ ℕ`, which makes `ℝ*` a *totally ordered* field and makes Łoś's theorem give every first-order
sentence a definite truth value. The calculus has a *theorem* about exactly this totalization:

- **`comparability_imp_llpo`** (`RealComparabilityLLPO.lean:33`, PURE, scan 2/0): if *any two* corpus
  reals (cut functions) are comparable `cutLe x y ∨ cutLe y x`, then **LLPO** holds — "the corpus reals
  are **not** constructively totally ordered."
- It delegates to **`llpo_of_realDichotomy`** (`RealDichotomyLLPO.lean:525`, PURE, scan 31/0): the real
  *sign* dichotomy "`x ≤ 1 ∨ 1 ≤ x`" already forces LLPO (the file's docstring: the exact sign-decision
  the bisection/IVT step needs *is* this LLPO act; the corpus stays ∅-axiom precisely because it never
  makes it).

The hyperreal's total order `[x] < [y]` (and Łoś's "`φ` is true iff `{n | φ(xₙ)}` is `𝒰`-large") is
**this very sign-decision performed for every pair at once** — the maximal, totalized version of the
comparison the calculus leaves as a partial modulus. So the ultrafilter is not an arbitrary choice the
repo declined to make; it is the **named non-constructive object** (`LPO`/`LLPO`,
`Omniscience.lean:25/:35`) that the calculus *defines as a `Prop` and calibrates against, never proves*.
The transfer principle is the omniscience act `Omniscience.lean` describes as "freeze a transition into a
verdict" — the move the residue refuses. **This is the located primitive: `𝒰`'s maximality = the
totalization that equals LLPO-strength, with no ∅-axiom witness.** Calibrated, not fatal.

### (3) The reification is the deeper break — the residue made an inhabited object

Even granting the sequence layer, the *classical* hyperreal `ε` is the residue **reified**: a definite
inhabitant smaller than every `1/n`. The calculus's residue is reached-by-none — `object1_not_surjective`
(`FlatOntologyClosure.lean:61`) says the surplus is outside *every* view's image; `cardinality.md` and
`ordinals.md` make the rule explicit (the diagonal/`ω` is *named by a finite signature, never
inhabited*). The ultrafilter is precisely the device that *inhabits* it: `𝒰` collapses "the sequence
points below everything" (a pointing, `q=±1`) into "`[(1/n)]` is a number." So the same primitive (`𝒰`'s
maximal totalization) does **both** breaking jobs — it totalizes the order (finding 2) *and* reifies the
residue (finding 3). The standard part `st(·)` is then the **residue-discarding reading**: it projects the
halo (the monad of infinitesimals around a finite hyperreal) back onto its real shadow — i.e. `st` *undoes*
the reification, mapping the reified object back to the pointing's limit. `st` is internal in spirit (it is
the limit-extraction `diagLimit`/`CauchyCutSeq.limit` already built, `padic.md`); it is `ℝ*`'s admission
that the reified `ε` had to be discarded to recover analysis.

### Net revelation

The hyperreal **splits at the quotient reading**: `⟨Hyper213 | L_cofin⟩` is internal and PURE (the
sequence, the infinitesimal-as-pointing, the constant embedding); `⟨Hyper213 | L_𝒰⟩` is the exterior
import, and it is the **single primitive `𝒰`-maximality** that does two forbidden jobs at once —
totalize the order (= LLPO-strength, `comparability_imp_llpo`) and reify the residue (against
`object1_not_surjective`). The boundary is the *same shape* `model_theory.md` found (the structural
skeleton is PURE; the specific maximal/saturating object is absent) and the *same calibration* the repo
uses for Bolzano–Weierstrass (`lpo_of_bw`, `BolzanoWeierstrass.lean:197`, PURE — BW ⟹ LPO, the
non-constructivity named and measured). No-exterior survives the stress test **as a claim under test**
(§5.4 guard): the internal handle (the cofinite quotient) is found and built; where no internal handle
exists (the ultrafilter's maximality), the note says so plainly and *measures* the gap at LLPO — it does
not declare a wall pre-emptively, nor suppress it reflexively.

## VALIDATE verdict — **LOCATED BOUNDARY** (calibrated, not fatal; one precise missing primitive)

This is NOT a clean EXTEND and NOT a fatal BREAK. It is a located, calibrated boundary, exactly the
outcome the README's REVELATION rule and `knots.md` license as valuable.

- **Internal (EXTEND) part:** the hyperreal *sequence* + *cofinite quotient* + *constant embedding* +
  *standard-part-as-limit* slot into the calculus with **no new primitive** — `C = Hyper213` (the
  modulus-free approximant sequence), `L = L_cofin` (the cofinite/Fréchet-filter reading), `Residue` =
  the limit tagged `q=±1`. Built and PURE (`Hyper213`, 7/0).
- **BREAK part (the located primitive):** the **non-principal ultrafilter `𝒰`** — specifically its
  *maximality* (deciding every `S ⊆ ℕ`). It is the genuine exterior import, and it is **calibrated**:
  the totalization it performs (total order + Łoś/transfer's definite truth values) is *exactly* the
  LLPO-strength sign-decision the calculus proves is non-constructive (`comparability_imp_llpo` →
  `llpo_of_realDichotomy`). It has **no ∅-axiom witness**, sitting with `LPO`/`LLPO` as a `Prop` the
  corpus states and calibrates against but never proves. The transfer principle and Łoś's theorem are
  **ABSENT** (no `transfer`/`Łoś`/`los_theorem` object exists — grep-confirmed empty), as expected:
  they require `𝒰`'s maximality.
- **Why this is calibrated, not fatal (the §5.1 verdict):** the ultrafilter is not a *new kind* of
  exterior — it is the *already-charted* omniscience axis (LPO/LLPO), the same wall as Bolzano–Weierstrass
  (`lpo_of_bw`) and the exact IVT sign-step (`RealDichotomyLLPO`). No-exterior is not refuted: the
  cofinite-quotient internal handle is found and built, and the irreducible remainder is *located and
  measured* at LLPO, not asserted as a god above the finite. The hyperreal is the cleanest stress test
  *because* it tries to reify the residue as an object; the calculus's answer is that the reifying device
  is precisely its named, measured non-constructive principle.

**Two-sided honesty (the horns of the test, decided):** (b) the INTERNAL horn is confirmed for the
*sequence/cofinite* layer (infinitesimal = pointing, ultrapower = sequence space, `st` = limit-discard);
(a) the BREAK horn is confirmed for the *ultrafilter* layer (totalization = reification = LLPO-strength,
no witness). The boundary runs exactly between cofinite (internal) and ultra (exterior) — between the
filter the residue admits and the maximality it refuses.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**The internal hyperreal sequence + cofinite quotient — `Hyper213` (7/0 PURE):**
- `lean/E213/Lib/Math/NumberSystems/Hyper/Hyper213.lean:43` `Hyper213` (`Nat → Raw`, modulus-free),
  `:46` `cofiniteEquiv`, `:49` `cofinite_refl`, `:52` `cofinite_symm`, `:57` `cofinite_trans`,
  `:67` `constHyper` (the `ℝ ⊂ ℝ*` embedding), `:70` `const_equiv_iff` (embedding faithful).
- `lean/E213/Lib/Math/NumberSystems/Hyper/Hyper213Tower.lean:63` `HyperTower`, `:67` `hyperTowerEquiv`,
  `:72` `hyperTower_refl` (the sequence-large × tower-large combination; scan 6/0 PURE). Docstring
  states the thesis: "ZFC's arbitrary-subset construction is not a primitive; large structure is built
  type-theoretically." (Note: `lensTowerHasDistinguishing` is flagged in-file as a classical-correspondence
  surface where `Quot.sound` enters via Lens `combine` — the named DIRTY edge, not used by the PURE
  theorems above.)

**The ultrafilter's totalization = LLPO (the calibrated exterior — the located primitive):**
- `lean/E213/Lib/Math/Logic/RealComparabilityLLPO.lean:33` `comparability_imp_llpo` (PURE, 2/0):
  comparability of any two corpus reals ⟹ LLPO — "not constructively totally ordered."
- `lean/E213/Lib/Math/Logic/RealDichotomyLLPO.lean:525` `llpo_of_realDichotomy` (PURE, 31/0): the real
  sign dichotomy `x ≤ 1 ∨ 1 ≤ x` ⟹ LLPO; `:517` `RealDichotomy` (def), `:532` `EncodedDichotomy`,
  `:539` `encodedDichotomy_of_llpo` (the two-sided calibration: the sign-decision IS exactly LLPO).
- `lean/E213/Lib/Math/Logic/Omniscience.lean:25` `LPO` (def), `:35` `LLPO` (def), `:40` `lpo_imp_wlpo`,
  `:59` `lpo_iff_wlpo_and_mp` (the omniscience ledger the ultrafilter sits on; scan 8/0 PURE).
- `lean/E213/Lib/Math/Logic/BolzanoWeierstrass.lean:197` `lpo_of_bw` (PURE): the calibration template —
  BW ⟹ LPO, "non-constructivity named and measured, not removed." (Module scan: all listed PURE.)

**The residue (reached-by-none — what the hyperreal reifies) — `FlatOntologyClosure` (7/0 PURE):**
- `lean/E213/Lib/Math/.../Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective`,
  `:47` `object1_injective` (faithful yet never total — the residue is outside every view's image;
  path: `lean/E213/Lens/Foundations/FlatOntologyClosure.lean`).

**Choice-as-Lens-spec (why 213 needs no exterior choice for its own quotients) — `Choice/Resolved` (PURE):**
- `lean/E213/Lib/Math/Foundations/Choice/Resolved.lean:34` `choice_as_lens_spec` (for any
  slash-congruence a concrete Lens exists, 0 external axioms — the *internal* choice, contrasted with
  `𝒰`'s *external* maximal one).

**The completeness-lens contrast (the modulus the hyperreal drops) — `ClassicalAnalysisCompletenessAsLens`:**
- `lean/E213/Lib/Math/Foundations/AxiomSystems/ClassicalAnalysisCompletenessAsLens.lean:54` `cauchyEquiv`,
  `:66` `completenessLens` — classical ℝ = triple composition using `Quot.sound` + `funext`; Hyper213's
  `cofiniteEquiv` is the *looser* (modulus-free) sibling.

**Scan tallies (`python3 tools/scan_axioms.py <module>`, from repo root):**
`Hyper213` 7/0 · `Hyper213Tower` 6/0 (PURE theorems; `lensTowerHasDistinguishing` is the named
classical-surface def, not a cited theorem) · `RealComparabilityLLPO` 2/0 · `RealDichotomyLLPO` 31/0 ·
`Omniscience` 8/0 · `BolzanoWeierstrass` all-PURE (module scan lists every theorem `[PURE]`) ·
`Choice.Resolved` PURE. All 0 DIRTY among cited theorems.

## Dropped / flagged

- **The non-principal ultrafilter `𝒰` — ABSENT, and provably non-constructive (the located primitive).**
  No `Ultrafilter`/`ultrafilter` object exists in `lean/E213` (grep-confirmed: the only `ultrafilter`
  hits are the *docstrings* of `Hyper213.lean` explaining it is the rejected primitive). Its maximality
  is the LLPO-strength totalization (`comparability_imp_llpo`), with no ∅-axiom witness. NOT asserted as
  built — named as the calibrated exterior.
- **Transfer principle / Łoś's theorem — ABSENT.** No `transfer`/`Łoś`/`los_theorem`/`losTheorem`
  object (grep-confirmed empty). They require `𝒰`'s maximality (definite truth value per statement on a
  `𝒰`-large set); without it, only the cofinite "eventually" survives, which gives `cofiniteEquiv` but
  not a decided truth value. Flagged as the open object the boundary forbids (the analogue of
  `model_theory.md`'s absent satisfaction relation, `padic.md`'s absent Ostrowski exhaustiveness).
- **`st(·)` / the halo / monad-of-infinitesimals — CONCEPTUAL.** No `standardPart`/`halo` object exists.
  The identification "`st` = the residue-discarding limit-extraction (`CauchyCutSeq.limit`/`diagLimit`,
  `padic.md`)" is the decomposition's reading, certified piecewise (the limit machinery is built); the
  named `st : ℝ* → ℝ` is absent because `ℝ*` (the ultra-quotient) is absent.
- **No claim that `Hyper213` IS the hyperreals.** It is explicitly the *cofinite* (Fréchet-filter)
  quotient — weaker than the ultrafilter quotient. Asserting `Hyper213 = ℝ*` would smuggle the
  ultrafilter; the note keeps the cofinite/ultra distinction as the boundary itself.
- **`Hyper213Tower.lensTowerHasDistinguishing` DIRTY edge — flagged, not cited.** The file's own
  docstring marks it a classical-correspondence surface where `Quot.sound` enters via the Lens `combine`
  function-equality. The cited theorems (`hyperTowerEquiv`, `hyperTower_refl`, `constHyperTower`) are
  PURE (scan 6/0); the `HasDistinguishing` instance is the named non-pure surface, not load-bearing here.
