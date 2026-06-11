# Cross-domain: the weld ↔ graded ladder / slot programme / Ricci arc (2026-06-11 merge)

Four identifications surfaced by merging main (slot programme, graded
rate ladder rungs 1–2 closed, π measure-modulus) into the weld branch
(`LowerBase` proven, `coth(1/q)` series ≡ CF unconditional).

## 1. The weld occupies rung 0, and the divider is partial-quotient growth

Main's ladder now has: rung `s` closed (`graded_total_modulus`,
`N = k^s + 1`), π conditionally degree-`s` (`pi_measure_modulus`) and
its Wallis pointing **rung ∞** (`wallis_no_graded_certificate` — every
schedule overtaken).  This branch populates the opposite pole: `coth(1/q)`
and `exp(2/q)` complete at **total modulus `k+2`, hypothesis-free**
(`cothSeriesCauchySep`, `expTwoOverQCFCauchySeq`) — transcendental
*values* whose natural pointings are rung-0.  What buys it is visible in
the pointing itself: the Lambert CF's partial quotients `(2J+1)q` **grow
linearly**, so cross-determinants shrink super-geometrically and the
det-one floor is effective separation for free.  π's natural pointings
have no such growth structure — rung ∞.  φ sits between: *bounded*
partial quotients, rung carried by the algebraic form margin
(`form_margin_modulus.md`), not by growth.

**Open direction**: state "the rung of a CF pointing is a readout of its
partial-quotient growth class" as a theorem schema — bounded pq → form
margin (algebraic), linearly growing pq → rung 0 (Padé/e-family),
structureless pq → no certificate (π's pointings).  The ladder's rung
would become a *computable invariant of the presentation*, sharpening
main's "the rung is of the pointing, not the real".

## 2. Inverse-avoidance by state-threading (the response to the slot wall)

Main's slot programme names the wall: the stable layer is killed by the
**escape of the inverse** (division kills `^`; `pow_lift_impossible` —
"tetration is not ×").  This branch's proofs are a systematic
demonstration of the constructive response: *never invoke the inverse —
thread the would-be-inverted quantity as state*.  Three instances, three
domains:

  - master identity (`LambertMasterId`): the weight `W(N,s)` and carrier
    `cc = 2N−2s+1` are threaded through the accumulator so the
    subtraction `2N−2s` **never forms**;
  - the budget (`budgetGen`): the per-step quotient `Mf/(2J+2)` never
    forms — the inequality is carried multiplied-out, and `wprod`
    cancels only at the very end (`Nat.le_of_mul_le_mul_left`);
  - Li–Yau (`gaussian_li_yau`, Ricci arc): `Δ log u ≤ 0` is proven as
    its division-free cleared form (log-concavity by cross-multiplication).

**Pattern to catalog**: where the slot analysis says "the inverse
escapes layer X", the working proof discipline is state-threading /
clearing — the inverse's *operand* is carried, the inverse itself is
never applied.  Candidate row for `catalogs/abstraction-candidates.md`.

## 3. Exclusion depth ≟ separation schedule (one lemma, two names)

Main's `BracketModulus.bracket_total_modulus`: two-sided shrinking
bracket + **exclusion depth** `B` ⟹ total modulus `N = B k + 2`
(π instance).  This branch's `AbCutSeq.sep_cauchy`/`toCauchySep`:
**separation schedule** `I` ("every false reading at resolution `k`
shows by layer `I k`") ⟹ modulus `N = I k` (exp(p/q) instance, and the
weld's W2 uses the same shape with `I k = k + 2`).  These look like one
lemma under two parametrizations.

**CLOSED** (`BracketModulus.bracket_is_sep_schedule`, ∅-axiom): the two
schemas **unify**.  Not as a literal `toCauchySep` instance — the carriers
sit at different abstraction levels (`bracket_total_modulus` on the bare
`rcut a d` Nat-fold, `toCauchySep` on a `Raw`-level `AbCutSeq`) — but the
*device* is one: the bracket's exclusion-depth hypotheses **imply
`sep_cauchy`'s `hsep` for the lower fold**, with the separation schedule
`I k = B k + 2`.  Any `false` reading of the lower fold anywhere shows at
layer `B k + 2`, by two regimes meeting there: `false` at a layer
`≤ B k + 1` propagates *forward* (`below_fwd`), `false` at a layer
`≥ B k + 2` reflects *back* by post-exit constancy (`bracket_cut_const`).
So the ladder's rung-2 bracket and the weld's completion engine are one
separation-schedule device — π/exp/coth differ only in who supplies the
schedule (two-sided shrinking bracket vs one-sided linear-pq growth).

## 4. The pair-layer cross expression: equivalence at 0, certificate at 1

Main's slot programme mints pair-classes by the cross-equation
(`a·d = b·c` — pairs-are-numbers, the witness layer beneath it).  The
weld lives on the *same expression* held at **1** instead of 0: the
det-one floor `P_i·devB_i = q²·devA_i·Q_i + 1` (descended
`cf_det_even_nat`) is what every order-transfer and the Casoratian
identity pivot on.  One pair-layer cross expression, two readouts:
`cross = 0` is an equivalence (a minted number), `cross = 1` is a
certificate (a margin that cannot vanish).  The Stern–Brocot/mediant
face already in the repo is the `cross = 1` *generator*; the slot
chapter's class-minting is the `cross = 0` *quotient*.

**Open direction**: a short essay or section stating the cross
expression as the one object, with `= 0` (class), `= 1` (unimodular
certificate), `≥ 1` (separation) as its three working regimes — and
whether the slot witness layer reconstructs the det-one floor when the
pair carries an order (directed pair = difference-Lens, §6.7).
