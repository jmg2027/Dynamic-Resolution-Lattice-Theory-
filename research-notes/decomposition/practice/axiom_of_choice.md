# Decomposition: the axiom of choice / LLPO (choice is a free Lens parameter σ, not an axiom)

*213-decomposition of "the axiom of choice / LLPO / the ultrafilter", per `../README.md`. This **corrects
and deepens** `SYNTHESIS.md` §2 finding (vii): the LLPO/choice point is NOT merely the "external/refused"
face of `B` — to stop at "213 refuses it" is a cop-out (the originator's correction, 2026-06-23).  The
213-native move is to **decompose the choice act itself**: a choice function is a **Lens** `σ`, different
choices (left/right/none) are different Lenses, and the operations extend *differently per σ* — `σ` is a
**free Lens parameter** (no exterior dialer fixes it, `seed/AXIOM/05_no_exterior.md` §5.1), exactly like the
p-adic "base" (`padic.md`) or the resolution dial.*

## The decomposition

- **Construction `C`** — a **family** `X : I → Type` with each fiber *inhabited* (the distinguishing has, for
  each index `i`, produced ≥1 distinguishable).
- **Reading `L_σ`** — a **section** `σ : ∀ i, X i` — a *choice function* = the Lens that reads **one
  distinguishable per fiber**.  **The choice function IS a Lens.**  Different rules — `σ_left` (first
  available), `σ_right` (last), `σ_min`, … — are **different Lenses** on the *same* `C`.
- **Residue `⊕`** — the **σ-dependence**: what *this* choice forgot (the non-selected fiber elements) and
  *how the operation's output depends on σ*.  `Residue(L_σ, C)` is parametrized by `σ`.

## Re-seeing the theorems — the dissolution (vs "assert AC" / "refuse AC")

Classical AC asks **"does a section exist?"** (`∏_i X_i ≠ ∅`) and you must **assert** it (AC) or **refuse**
it (constructive / ¬AC).  213 dissolves the question: *applying a Lens is an **act**, not an existence claim*
(CLAUDE.md "Lens application IS a residue self-pointing event").  So you never assert "a section exists"; you
**apply a section-rule** (`σ_left`, `σ_right`, …) and read.  The "non-constructive strength" is precisely the
fact that **no section-Lens is forced/canonical** — there is no exterior dialer (§5.1) that selects *the* `σ`.
Hence:

> **`σ` is a FREE Lens parameter.**  "AC is true" = *any* `L_σ` may be applied; "AC is refused" = *no* `L_σ`
> is canonical.  These are **not in conflict** — together they say `σ` is free.  The operations (sup,
> product, ultrafilter, well-ordering, Hahn–Banach, standard-part) become **σ-parametrized**: 213 carries
> `σ` explicitly and computes per-`σ`, where the classical mathematician *hides* it ("by AC, choose …").

The originator's own examples are exactly the σ-readings: `σ_left` vs `σ_right` (pick the left/right element)
are two Lenses carried in parallel; "can choose" (`L_σ` applied) vs "cannot choose" (work with the unselected
family / the truncation `∥∏X∥`) are two readings; the operation **branches by `σ`**.

## The deep tie: LLPO = the `q=±1` choice-Lens, *unforced*

`LLPO` (`Lib/Math/Logic/Omniscience.lean:35`): for `f : ℕ→Bool` with at most one `true`, *either* `f` is
false on all even indices *or* on all odd indices — the (possible) true index is **even or odd**, undecidably
which.  In 213 this is a **binary choice-Lens**: `σ_even` ("read the true as even-indexed") and `σ_odd` are
two *total* readings, and LLPO-undecidability = **neither is forced**.  But a binary choice (`{left, right}`,
`{even, odd}`) over a 2-element fiber **IS the `q=±1` residue tag `B`** (`escape`/`converge`, ∓1).  So:

> **LLPO = the `q=±1` tag as a free Lens parameter** — choice over binary fibers is exactly `B`, and
> "can't decide which" = "no exterior dialer fixes the ±1 bit".  Finding (vii)'s "external/refused face" is
> corrected: LLPO is not a *wall* 213 refuses, it is the **freedom of the `B`-valued `σ`**.  The diagonal
> (internal face) says the residue *exists* (reached-by-none); the choice-Lens `σ` is *which point of that
> residue you point at* — free.  The five calibrated boundaries (ultrafilter, standard-part, well-ordering,
> …) are the operations that each **carry this free `σ`**; "converging on choice" = "all parametrized by the
> same free `σ`".

## Revelation (collapse + forcing)

**Collapse — "AC true vs AC false" is one free parameter, two policies.**  The assert/refuse dichotomy is
the *import* (a forced exterior `σ`-verdict); 213 has no exterior (§5.1), so `σ` is internal and free, and
the dichotomy dissolves into "`σ` is a Lens parameter; compute per-`σ`".

**Forcing — 213's "σ is free" PREDICTS the independence of AC.**  If `σ` is a free Lens parameter, then *both*
a choice-policy and its negation may be **adjoined** consistently — which is exactly **Cohen forcing /
Gödel–Cohen independence**: forcing *adjoins a generic `σ`*, and AC's independence from ZF is the statement
that `σ` is unconstrained by the construction.  So the 213 reading is not a refusal — it is the *reason* AC
is independent: a free Lens parameter has no forced value, hence both adjunctions are consistent.  (Honest
scope: this is a **dissolution + a structural prediction of independence**, NOT a proof or disproof of AC —
213 proves neither AC nor ¬AC, by design; it relocates them to a free `σ`.)

**Per-σ constructivity (why 213 needs no AC).**  Each `L_σ` is *data* — an explicit section/rule.  On a
*concrete* inhabited family with an explicit element-rule, `L_σ` is constructive, ∅-axiom, no AC.  The
non-constructive content appears *only* when one demands a uniform canonical `σ` with **no** rule — which 213
says does not exist (no exterior).  So the calculus never asserts a canonical `σ`; it parametrizes.  See the
∅-axiom witness `ChoiceLens.lean` (below): two explicit sections of one inhabited family, an operation that
differs under them, **no Classical**.

## Verified Lean anchors (file:line:theorem — grep-confirmed)

- `Lib/Math/Logic/Omniscience.lean:25 LPO`, `:35 LLPO` (the choice-strength `Prop`s 213 states-but-never-proves
  — i.e. the free `σ` made explicit), `:59 lpo_imp_wlpo` (the constructive ∅-axiom deductions that hold with
  *no* `σ` fixed — "the residue's free interior").
- The free-`σ` rationale: `seed/AXIOM/05_no_exterior.md` §5.1 (no exterior dialer ⟹ no forced parameter).
- The binary-choice = `B` link: `Lib/Math/Foundations/ResidueTag.lean` (`multiplier_unimodular`,
  `residue_tag_two_poles`) — the `q=±1` tag the LLPO even/odd `σ` instantiates.
- ∅-axiom witness (BUILT this push, **12/0 PURE**, independently re-verified): `Lib/Math/Logic/ChoiceLens.lean`
  — `:60 sigmaL`/`:64 sigmaR` (two explicit total sections of `F i := Bool`, no AC), `:71
  readOp_sigma_dependent` (`readOp sigmaL 3 ≠ readOp sigmaR 3` — the operation depends on `σ`), `:81
  choice_is_free_lens_parameter` (the point: distinct sections + σ-dependent op), and the LLPO tie-in `:98
  sigmaEven_ne_sigmaOdd_at_0` / `:114 readOp_even_odd_differ_at_1` (the even/odd binary `σ`).

## BUILT vs ABSENT

- **BUILT (∅-axiom):** the omniscience ledger (`LPO`/`LLPO` as `Prop`s + the choice-free deductions between
  them, `Omniscience.lean`); the `q=±1` tag the binary `σ` instantiates; the per-`σ` constructive witness
  (`ChoiceLens.lean` 12/0, two explicit sections, operation σ-dependent — choice as a Lens parameter, no AC).
- **ABSENT (predicted-not-built):** a *general* σ-parametrized operation library (ultrafilter / well-order /
  Hahn–Banach each carried with an explicit `σ`); the forcing/independence statement as a Lean theorem
  (`σ` free ⟹ both adjunctions consistent — the deep prediction, a model-theoretic build).

## Touches the model?

**No new primitive — `σ` is a Lens parameter (like the p-adic base / the resolution dial), and over binary
fibers it IS `B`.**  The advance corrects finding (vii): the LLPO/choice point is not the "refused" face of
`B` but the **freedom of the choice-Lens `σ`** — `σ` unforced because there is no exterior (§5.1).  The
assert/refuse dichotomy is dissolved (compute per-`σ`); AC's independence is *predicted* (a free parameter
admits both adjunctions = forcing).  The honest boundary: 213 proves neither AC nor ¬AC — it relocates the
question to a free Lens parameter, which is a *deeper* answer than refusal, exactly as the originator demanded.
