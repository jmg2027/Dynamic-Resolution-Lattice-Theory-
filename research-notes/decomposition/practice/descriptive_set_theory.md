# Decomposition: descriptive set theory (Borel / projective hierarchy, analytic⊋Borel, perfect set, determinacy)

*213-decomposition of "the definable sets of reals" — per `../README.md` (model v7.1) and the
directly-related `cardinality.md` (the count-reading's forced diagonal = the limitative engine,
Residue tagged `q=±1`), `godel.md` (the escaping diagonal on a *coded* self-cover), `ordinals.md`
(the fold-height reading run past every finite stage = the hierarchy rank), `measure.md` (Borel /
measurable sets as the `q=+1` corner; non-measurable = the `q=−1` Choice diagonal), and
`game_theory.md` (P/N positions = the `q=±1` poles).*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — distinguishing, iterated. A "set of reals" is not a primitive container; it is
  a **family of distinguishables** specified by a finite *recipe* (a `Raw` build-tree). A real is itself
  a pointing (an approximant sequence, `Real213`-cut); a definable set is a construction *over* those
  pointings. Crucially the recipe carries a finite signature — its build-tree depth — exactly the
  `Raw.depth`/nesting of `ordinals.md`. The "set" is the recipe, not a completed extension; no exterior
  container is assumed (names land back inside `Raw`, the same internality `godel.md` uses via
  `Raw.toNat_injective`).
- **Reading `L↑` (the hierarchy / fold-height reading)** — project a set-recipe to *how many folds*
  (countable unions, complements) built it. This is `ordinals.md`'s height-reading `L↑` = `Raw.depth`
  read on *set*-constructions instead of number-constructions: each Borel level `Σ⁰_α`/`Π⁰_α` is **one
  more fold** (a countable `∪`, or a complement), and the **level index α is the fold-height ordinal**
  — the order-type of the build below it. One more `∪`/complement = `+1` to the height
  (`MuNuMirror.ascent_adds_unit`), exactly as a successor ordinal is.
- **Direction sub-bit (the `q=±1` swap) `L↑` carries** — complementation `Σ⁰_α ↔ Π⁰_α` is the
  *negation involution*: the same orientation/swap bit that flips sign in ℤ, `det`, `∂`, the Lie
  bracket. `Σ` (built by `∃`/`∪`, the open pole) and `Π` (built by `∀`/`∩`/complement, the closed
  pole) are **one reading at its two unimodular signs**, not two readings. The dual classes are the
  `q=±1` reflection of the *same* fold-height.
- **Residue (the `q=−1` escape: analytic ⊋ Borel) `q=−1`** — what the fold-height reading **forces
  but cannot capture**: a *projection*. An analytic set `Σ¹₁` = "∃ a real `y` such that `(x,y) ∈ B`"
  for `B` Borel — a quantifier over the *uncountable* continuum of reals. That `∃ y : real` is a
  **self-cover re-entering itself**: it indexes the set by an uncountable family the Borel
  fold-tally cannot exhaust, and Suslin's theorem (analytic ⊋ Borel) says it lands *outside* every
  Borel level. This is **exactly** `cardinality.md`'s `q=−1` escape diagonal
  (`object1_not_surjective` / `no_surjection_of_fixedpointfree`) **relocated onto the set hierarchy**:
  a `Σ¹₁`-complete set is "the value outside the Borel image", the same fixed-point-free escape that
  outruns every level (`DepthHeightDiagonal.height_diagonal_escapes` = the global diagonal one scale
  up). Projection is the diagonal; the analytic-non-Borel jump is that diagonal made a *hierarchy
  theorem*.

## Re-seeing — the hierarchy is the fold-height axis, the jump is the diagonal escape

```
   "definable set of reals" =  ⟨ a set-recipe over real-pointings | — ⟩        (C, before any reading)
   Borel level Σ⁰_α / Π⁰_α  =  ⟨ recipe | L↑ = fold-height, read as ordinal α ⟩  (one more ∪/¬ = +1; ascent_adds_unit)
   complementation Σ↔Π       =  the q=±1 swap-bit of L↑                          (negation involution)
   Borel = ⋃_{α<ω₁} Σ⁰_α     =  the unbounded fold-ascent's order-type cap, q=+1   (ascent_unbounded; ω₁ = the limit pole)
   analytic Σ¹₁ (projection) =  Residue(L↑, C), q=−1                             (the ∃-real diagonal escaping every level)
   Suslin: analytic ⊋ Borel  =  P(⟨ projection self-cover | L↑ ⟩)  — no Borel level realises it
                                = object1_not_surjective relocated onto the set hierarchy
   perfect set property       =  cardinality.md's uncountable diagonal on an analytic set
   determinacy (det / undet)  =  the q=±1 game-value tag (P/N), game_theory.md
   projective hierarchy Σ¹_n  =  L↑ iterated ABOVE the diagonal (projection ∘ complement, n times)
```

The Borel hierarchy reads a set-recipe *as its own fold-tally*, level by level — the **same**
`L↑`/`Raw.depth` ascent `ordinals.md` runs, only the carrier is sets rather than numbers. The ordinal
height `α<ω₁` is the well-founded build-rank (`Lambek.isPart_wf`, `Lambek.part_depth_lt`): the
Borel hierarchy is well-ordered for the same reason the ordinals are — the peel relation on recipes is
well-founded, no infinite descent (`Lambek.no_infinite_descent`). `ω₁` (the Borel closure point) is the
*converging* `q=+1` residue of the unbounded countable-fold ascent (`MuNuMirror.ascent_unbounded`:
`∀N, ∃r, N<r.depth` — no finite cap), named by its generator, never inhabited — exactly as `ordinals.md`
caps honestly at `ω` and names `ε₀`'s direction only.

The single change from Cantor to Suslin is the *carrier of the self-cover*: `cardinality.md` reads a
family of distinguishables (the diagonal `!(f x x)` escapes every enumeration); descriptive set theory
reads a family of *Borel set-recipes* (the projection `∃y. (x,y)∈B` escapes every Borel level). Same
engine `g a := t(f a a)` (`OneDiagonal.lawvere_fixed_point`, `russell_liar_no_surjection`,
`one_diagonal_generates`), `t` fixed-point-free, `q=−1` — the precise pattern `godel.md` reused for
provability. The projective hierarchy `Σ¹_n/Π¹_n` is then the diagonal *iterated*: project (`∃`,
`q=−1` escape), complement (`q=±1` swap), repeat — the fold-height axis continued *above* the first
diagonal, each level a residue-of-a-residue (the spectral-sequence-style re-entry the corpus already
names, `ResidueReentry`).

## Revelation (collapse + residue-surfaced + located boundary)

**Collapse.** The Borel hierarchy, the ordinal hierarchy (`ordinals.md`), and the arithmetic hierarchy
(`godel.md`) are **one fold-height reading** read on three carriers (sets / build-depth / formulas);
the level index is the same well-founded rank in all three. Complementation `Σ↔Π`, sign in ℤ/`det`/`∂`,
and the negation involution are **one `q=±1` swap-bit**. So descriptive set theory adds **no new
primitive**: it is `ordinals.md`'s `L↑` (fold-height, the hierarchy) + the `q=±1` complementation swap
+ `cardinality.md`/`godel.md`'s `q=−1` escape diagonal (projection / Suslin), all three at once on sets.

**Residue-surfaced (the new datum of this note).** Suslin's analytic ⊋ Borel is the calculus's `q=−1`
escape diagonal **made into a hierarchy theorem**. Where `cardinality.md` shows the diagonal escapes a
*flat* enumeration and `ordinals.md` shows the height-residue escapes one scale up, descriptive set
theory shows the *same* escape stratified by ordinal height: projection (`∃` a real) is precisely the
self-cover re-entry that no Borel level (no finite-fold recipe) can capture — a `Σ¹₁`-complete set is
the literal "value outside the Borel image", `object1_not_surjective`/`height_diagonal_escapes` worn as
"analytic is bigger than Borel". The perfect set property (every uncountable analytic set contains a
perfect set ≅ the continuum) is `cardinality.md`'s uncountability diagonal landing *inside* the analytic
class — the `q=−1` residue's continuum, not a new cardinal above it. Determinacy (a game's value: a
win/lose, determined/undetermined tag) is the `q=±1` pole bit of `game_theory.md` (P-position = `q=+1`
converging fixed point; N-position = `q=−1` bounded-diagonal escape, `mex_eq_zero_iff_zero_excluded`),
transported onto the payoff sets of the hierarchy.

**Located boundary (honest — and like non-standard analysis's ultrafilter at LLPO).** The hierarchy's
*lower reaches* (Borel = the well-founded fold-ascent; the first escape Σ¹₁) decompose cleanly with the
built engine. The *higher reaches* are a **calibrated non-constructive boundary**, not an EXTEND:
- **Borel determinacy** (Martin) provably needs the full power-set / iterated-ℵ machinery (Friedman:
  not provable in finite-order arithmetic) — it consumes the `q=+1` ascent past every level the corpus
  inhabits.
- **Projective determinacy / analytic perfect-set-property** need *large cardinals* — strictly beyond
  any ∅-axiom witness, the `q=−1` escape iterated transfinitely with no finite signature available.
- **The reified `ω₁`-completed Borel σ-algebra and "every uncountable analytic set has a perfect
  subset for *all* projective levels"** annex the `q=−1` half by adjoining Choice/large cardinals —
  the same move `measure.md` flags (the countable-cover infimum / non-measurable-set half it omits).
This is the analogue of `nonstandard_analysis.md`'s ultrafilter calibrated at LLPO: the *internal*
horn (the finite-fold Borel ascent, the first diagonal escape) is the `q=+1`/diagonal corner the
corpus owns; the irreducible remainder (Choice-/large-cardinal-strength determinacy and the completed
projective hierarchy) is **measured, not posited as a wall** — it sits exactly where the fold-height
ascent leaves the finite signature behind, the `ordinals.md` cap relocated to `ω₁` and beyond.

## VALIDATE — verdict

**PREDICTION + located non-constructive boundary** (no break; no new primitive). The model EXTENDS
through the *interior*: the Borel hierarchy = the fold-height axis `L↑` indexed by ordinals
(`ordinals.md`), complementation = the `q=±1` swap, and analytic⊋Borel (Suslin) = the `q=−1` escape
diagonal (`cardinality.md`/`godel.md`) made a hierarchy theorem — three already-built mechanisms, one
new carrier (sets of reals). The new datum is genuinely new (not a re-skin of cardinality/ordinals):
the **diagonal-escape graded by ordinal height on sets**, with Suslin's jump = the diagonal-as-hierarchy
and Σ↔Π = the complementation swap. The named field objects (`BorelHierarchy`, `analytic`/`Σ¹₁`,
`Suslin`, `Wadge`, `determinacy`, `perfect_set`) are **predicted-not-built** (grep-confirmed absent).
The boundary is honest and calibrated: Borel determinacy needs the full ascent, projective
determinacy / the perfect-set property at projective levels need large cardinals — located exactly at
the `q=±1`/`ω₁`-and-beyond corner where the finite signature is left behind, the same kind of measured
remainder as non-standard analysis's ultrafilter at LLPO.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scanned ∅-axiom

The fold-height / hierarchy axis (the Borel-level ordinal rank):
- `Theory/Raw/Lambek.lean:187:part_depth_lt`, `:199:isPart_wf`, `:273:no_infinite_descent`
  (the level-ordinal is well-founded — the hierarchy is well-ordered; **22 pure / 0 dirty**)
- `Theory/Raw/MuNuMirror.lean:50:ascent_unbounded` (`∀N,∃r,N<r.depth` = the unbounded
  countable-fold ascent capping at `ω₁`, `q=+1`), `:59:ascent_adds_unit` (one more ∪/¬ = depth `+1` =
  successor level), `:80:succ_not_idempotent` (the growing iteration-character of the hierarchy; **8
  pure / 0 dirty**)
- `Lib/Math/Analysis/Cauchy/DepthHeightDiagonal.lean:56:height_diagonal_escapes`,
  `:71:epsilon_direction` (the height-residue one scale up = the projective continuation direction;
  **38 pure / 0 dirty**)

The `q=−1` escape diagonal (analytic ⊋ Borel / Suslin = projection escapes every level):
- `Lens/Foundations/FlatOntologyClosure.lean:61:object1_not_surjective`, `:47:object1_injective`,
  `:69:self_covering_closure` (the self-cover faithful yet never total = the Σ¹₁-complete "outside the
  Borel image"; **7 pure / 0 dirty**)
- `Lens/Foundations/OneDiagonal.lean:43:lawvere_fixed_point`, `:51:no_surjection_of_fixedpointfree`,
  `:87:russell_liar_no_surjection`, `:101:one_diagonal_generates` (the one escape engine `g a:=t(f a a)`,
  `t` fixed-point-free; projection `∃y` is its set-carrier instance; **11 pure / 0 dirty**)
- `Lens/Cardinality/Godel.lean:118:Raw.toNat_injective`, `:131:raw_at_most_countable` (the coding /
  internality the `∃`-quantifier rides — names land back inside)

The `q=±1` tag (complementation Σ↔Π; determinacy P/N):
- `Lib/Math/Foundations/ResidueTag.lean:73:ResidueTag` (inductive escape|converge),
  `:86:multiplier_unimodular`, `:133:escape_residue_outside`, `:160:converge_residue_fixed`,
  `:180:golden_is_converge`, `:228:residue_tag_two_poles` (the formal `q=±1` two-poles object;
  **55 pure / 0 dirty**)
- `Lib/Math/Combinatorics/Mex.lean:153:mex_eq_zero_iff_zero_excluded`, `:95:mexFrom_finds`,
  `:72:mexFrom_lt_mem` (the determinacy/game P=`q=+1` ⟺ `0` excluded vs N=`q=−1` bounded diagonal;
  **12 pure / 0 dirty**)

Cross-note anchors (grep-confirmed in neighbors):
- `measure.md` — Borel/measurable = the `q=+1` corner; non-measurable/Vitali = the `q=−1` Choice
  diagonal (`object1_not_surjective` at `FlatOntologyClosure.lean:61`), the same diagonal this note
  grades by ordinal height.
- `ordinals.md` — the fold-height residue / `ω` cap (`ascent_unbounded`); `ω₁` here is the same cap on
  the *countable-fold* ascent.
- `cardinality.md`, `godel.md` — the `q=−1` escape engine on the count/provability carriers; this note
  is its set-hierarchy carrier.

## Dropped / flagged

- **No `Borel` / `BorelHierarchy` / `analytic` / `Σ¹₁` / `Suslin` / `Wadge` / `projective` /
  `perfect_set` / game-`determinacy` Lean object exists** — grep over `lean/E213/` confirms: matches
  for "Borel" are all *Heine–Borel* compactness (`Geometry/Topology/`, `Logic/WKLHeineBorel.lean`);
  "analytic" is real-analysis usage; "determinacy" appears only as `Theory/Raw/StateMachine.lean:18`
  ("behaviour fixed by transition", a finality property, **not** game determinacy); "hierarchy"
  matches are physics mass-towers / FSM-arithmetic, unrelated to the Borel/projective hierarchy. All
  field-named objects are recorded **predicted-not-built**, not cited as proven.
- **No verified buildable witness proposed.** The honest buildable target would be a *finite-fold*
  Borel-level recipe type `{r : Raw // r.depth ≤ n}` with complementation as the `q=±1` swap and a
  *projection* operation whose image provably escapes every finite level (instantiating
  `object1_not_surjective` on set-recipes) — i.e. a toy "analytic ⊋ Borel_n at finite n". This is named
  as the open promotion target; **not asserted built and no `decide` witness proposed** (the corpus has
  the engine but no set-recipe carrier wired to it, mirroring `godel.md`'s "engine built, the specific
  named cover is the open instance").
- **Borel determinacy / projective determinacy / projective-level perfect-set property** flagged as the
  **calibrated non-constructive boundary** (full ascent / large cardinals) — located, not forced into
  EXTEND.
