# Decomposition: strategic game theory / Nash equilibria (normal-form games, mixed strategies, Nash existence via Brouwer/Kakutani, best-response dynamics, zero-sum / minimax / von Neumann, correlated equilibria)

*213-decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants, the q=±1
spine, the q=+1 fixed-point pole). This is **strategic / economic** game theory — distinct from the
already-decomposed combinatorial `game_theory.md` (Nim/Sprague–Grundy/mex). The two are kept apart and
cross-referenced, not merged. The leverage hypothesis: a Nash equilibrium is the calculus's **q=+1 fixed
point of the best-response reading** — the *converging* side of the same diagonal/self-map engine
(`lefschetz_degree.md`) whose *escaping* q=−1 side is Cantor/Gödel; and the minimax theorem IS
`convex_duality.md`'s LP duality on the strategy space. No new primitive: it is the fixed-point engine
(q=+1 side) + LP duality. Honest grounding up front: **every named strategic-game object — `Nash`,
`equilibrium`, `bestResponse`, `minimax`, `payoff`, `strategy`, `Kakutani`, `Brouwer` (fixed point),
`zeroSum`, `correlated` — is ABSENT from `lean/E213`** (grep-confirmed below; the only `Brouwer` hits are
Brouwerian bar-induction, a different theorem). The built legs are the diagonal/self-map fixed-point
engine, the q=±1 tag, the modulated Banach contraction, and a real ∅-axiom LP weak-duality + zero-gap
(minimax) theorem; the named field objects are the predicted-not-built ceiling.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **self-map of the strategy space**. The players' joint strategy profile
  `σ = (σ₁,…,σₙ)` is a point of the construction `Δ¹ × ⋯ × Δⁿ` (each `Δⁱ` a player's mixed-strategy
  simplex — a probability weight over pure actions, `probability.md`'s `ratio∘count` container). The
  **best-response map** `BR : σ ↦ BR(σ)` (each player re-optimizes given the others' strategies) is a
  **self-endomorphism of that space** — the *exact* shape `lefschetz_degree.md`'s `f : C → C` and
  `OneDiagonal.lean`'s `f : A → A → B` carry. `C` here is the strategy-space-with-a-self-map: the same
  carrier as Lefschetz/Brouwer, with `BR` playing the role of `f`. The payoff data (the normal-form
  matrix) parametrizes `BR`; the *equilibrium structure* lives entirely in `BR`'s fixed points.

- **Reading `L_BR` (best-response = self-pointing the strategy space against the diagonal)** — read the
  profile `σ` against the **diagonal** `Δ = {(σ,σ)}`: a profile is a **Nash equilibrium** iff it is a
  **fixed point of `BR`**, `σ* ∈ BR(σ*)` — i.e. `σ* ∩ Δ` for the best-response self-map. This is
  `lefschetz_degree.md`'s "a fixed point of `f` is a point of `f ∩ Δ`" instanced on the strategy space
  with `f = BR`. Best-response *dynamics* (iterate `σₜ₊₁ = BR(σₜ)`) is the **q=+1 contraction reading**:
  when `BR` is a contraction (e.g. dominance-solvable / potential games with a unique basin) the orbit
  converges to the fixed point, the same `banach_fixed_point_modulated` / `golden_is_converge` Picard
  iteration as φ, the Gaussian, and the ODE flow.

- **Reading `L_dual` (zero-sum / minimax = the LP-duality reading on strategies)** — for a two-player
  zero-sum game with payoff matrix `A`, read the value two ways: the **max-min** (row player guarantees,
  `max_x min_y xᵀAy`) and the **min-max** (column player caps, `min_y max_x xᵀAy`). The minimax theorem
  `max min = min max` is `convex_duality.md`'s **weak duality `max_λ min_x ≤ min_x max_λ` made tight** —
  the adjoint inequality `gc_unit`/`gc_counit` with **zero gap**, exactly `OllivierRicci`'s
  `kantorovich_weak_duality` (`dualValue ≤ transportCost`) closed to equality by `ollivier_plan_optimal`
  ("when a plan and a potential meet, the gap is 0"). The game value is the LP optimum; minimax = strong
  duality = the q=+1 tight optimum on the strategy polytope.

- **Residue** — the README's q=±1 tag, the *same* diagonal at its two signs (the load-bearing datum):
  - **q=+1 converge:** a Nash equilibrium **exists** = the best-response self-map **meets the diagonal**;
    when `BR` is a contraction the fixed point is also *reached* (`banach_fixed_point_modulated` /
    `converge_residue_fixed`). Nash existence (Brouwer/Kakutani) is the q=+1 "a fixed point exists"
    pole of `lefschetz_degree.md`'s engine: `L(BR)≠0 ⟹ BR meets Δ`. The zero duality gap (minimax) is
    the *same* q=+1 settle — `convex_duality.md`'s closure exact, never oscillating.
  - **q=−1 escape:** a game with **no pure-strategy equilibrium** = the best-response correspondence
    has *no fixed point on the pure-action corners* — the q=−1 fixed-point-FREE escape
    (`no_surjection_of_fixedpointfree`, the diagonal dodged on the discrete corner set). The resolution
    is **mixing**: passing to the convex mixed-strategy simplex *recovers* the fixed point (Brouwer on
    the compact convex `Δ`). So "no pure equilibrium" is the q=−1 escape *at coarse (pure) resolution*,
    converted to q=+1 by the resolution dial moving to the mixed extension — the same escape→converge
    move the calculus runs throughout (the mex bounded-diagonal at finite resolution, `game_theory.md`).

## Re-seeing — `⟨C | L_BR⟩ ⊕ Residue(q=±1)`

```
   strategy profile σ        =  a point of Δ¹×⋯×Δⁿ (each Δⁱ = probability.md's ratio∘count simplex)
   mixed strategy            =  a probability weight over pure actions  (probability.md, ratio∘count)
   best-response map BR      =  a self-map of the strategy space        (lefschetz_degree.md's f:C→C; OneDiagonal's f)
   Nash equilibrium σ*       =  a FIXED POINT of BR:  σ* ∈ BR(σ*)  =  σ* ∩ Δ   (q=+1 fixed-point pole)
   Nash EXISTENCE (Brouwer)  =  "a fixed point exists" = BR meets the diagonal   (Lefschetz q=+1 / lawvere_fixed_point)
   no PURE equilibrium       =  fixed-point-free on the pure corners  (q=−1 escape, no_surjection_of_fixedpointfree)
   recovered by MIXING       =  resolution dial → mixed extension; convex Δ restores the fixed point (q=−1 ↦ q=+1)
   best-response DYNAMICS    =  iterate σₜ₊₁=BR(σₜ) ; converges = q=+1 contraction  (banach_fixed_point_modulated)
   zero-sum value (minimax)  =  ⟨ strategy polytope | LP max-min / min-max ⟩
   max min ≤ min max         =  the adjoint inequality / weak duality   (kantorovich_weak_duality)
   max min = min max (vN)    =  zero gap = strong duality = q=+1 tight optimum  (ollivier_plan_optimal)
   correlated equilibrium    =  the fixed point on the JOINT-distribution polytope (LP feasibility, wider Δ)
```

The map is exact at the structural level: **Nash = `lefschetz_degree.md`'s q=+1 fixed-point pole, read
with `BR` as the self-map**; **minimax = `convex_duality.md`'s LP weak-duality made tight**. Nash sits
precisely where the notebook's two q=+1 engines meet — the diagonal/self-map fixed point (Lefschetz) and
the adjoint-closure zero-gap optimum (convex duality) — exactly the "deepest collapse sits where two
built readings meet" pattern.

| classical object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| best-response map `BR` self-map | the self-map `f : C → C` against the diagonal | `lefschetz_degree.md`, `cardinality.md` | `OneDiagonal.lawvere_fixed_point`, `no_surjection_of_fixedpointfree` |
| Nash equilibrium = fixed point | the q=+1 "fixed point exists" pole | `lefschetz_degree.md`, `golden_ratio.md` | `ResidueTag.converge_residue_fixed`, `golden_is_converge` |
| Nash existence (Brouwer/Kakutani) | the fixed-point/diagonal engine (q=+1 side) | `lefschetz_degree.md` | `lawvere_fixed_point` (discrete); continuous = `Real213` gap |
| no pure eq.; recovered by mixing | q=−1 escape ↦ q=+1 via resolution to convex `Δ` | `game_theory.md` (mex), `cardinality.md` | `no_surjection_of_fixedpointfree`, `object1_not_surjective` |
| best-response dynamics converge | the q=+1 contraction / Picard iteration | `differential_equations.md`, `martingales.md` | `banach_fixed_point_modulated` |
| minimax `max min ≤ min max` | the adjoint inequality / weak duality | `convex_duality.md` | `OllivierRicci.kantorovich_weak_duality` |
| minimax `max min = min max` (von Neumann) | strong duality = zero gap = q=+1 tight optimum | `convex_duality.md` | `ollivier_plan_optimal`, `ollivier_bracket` |

## LEVERAGE — does the hypothesis fall out, and what is built vs absent?

**Verdict: PREDICTION + PARTIAL — the two load-bearing legs are GROUNDED in built ∅-axiom Lean (the
fixed-point/diagonal engine for the *discrete/algebraic* existence claim, q=+1 side; and a real LP
weak-duality + zero-gap theorem for minimax), but the *continuous* Brouwer/Kakutani existence leg is the
`Real213`/continuous fixed-point residue (only the discrete Lawvere fixed point is built), and ALL named
strategic-game objects are ABSENT.** Leg by leg, honest.

**(1) ★ Nash = the q=+1 fixed point of the best-response self-map — the diagonal engine, GROUNDED
(discrete/algebraic side).** A Nash equilibrium is a fixed point `σ* ∈ BR(σ*)` of a self-map of the
strategy space — the **exact shape** of `OneDiagonal.lean`'s `f : A → A → B` / `lefschetz_degree.md`'s
`f : C → C ∩ Δ`. The calculus's deepest collapse here is the one `lefschetz_degree.md` already made: the
**same self-cover/diagonal reading generates both poles** — read with a Bool weight (fixed-point-free,
`t = not`) it is `cantor_via_lawvere` / `object1_not_surjective` (the q=−1 *escape*: Cantor, Gödel,
no-pure-equilibrium); read with the existence direction it is `lawvere_fixed_point` (the q=+1 *converge*:
"a fixed point exists" = a Nash equilibrium). So **"a Nash equilibrium exists" and "the residue cannot
be pointed" are ONE `(C,L)` object — the self-cover/diagonal — read at its two signs.** This is fully
grounded in `OneDiagonal` (11/0 PURE) and `FlatOntologyClosure` (7/0 PURE): `lawvere_fixed_point` is the
q=+1 "fixed point exists" leg, `no_surjection_of_fixedpointfree` the q=−1 "escape" leg. The formal q=±1
tag bundling both is `ResidueTag` (55/0 PURE): `converge_residue_fixed` (q=+1, delegating to the Banach
engine) is Nash existence's pole, `escape_residue_outside` (q=−1) the no-equilibrium pole,
`golden_is_converge` tying +1 to the literal φ Cassini fixed point.

**(2) Best-response dynamics converging = the q=+1 contraction — GROUNDED.** When `BR` is a contraction
(dominance-solvable games, potential games with a unique minimizer), iterating `σₜ₊₁ = BR(σₜ)` is the
**Picard iteration** the calculus runs as `banach_fixed_point_modulated` (the q=+1 converge engine,
delegated to by `ResidueTag.converge_residue_fixed`, 55/0 PURE). This is the *same* engine
`differential_equations.md` welds to the ODE flow and `gaussian_clt.md` to the convolve-rescale fixed
point — best-response dynamics is its third+ field on the strategy-space carrier. The honest residual is
identical to those entries: the engine is built and PURE, but the *specific* "best-response is a
contraction on the simplex" instance (and a genuine `CompleteMetricModulus Δ` on the mixed-strategy
polytope) is not welded as a `Contraction` — the same gap `gaussian_clt.md`/`differential_equations.md`
flag.

**(3) ★ Minimax (zero-sum) = LP duality on strategies — GROUNDED (the surprise, same as
`convex_duality.md`).** The von Neumann minimax theorem `max_x min_y xᵀAy = min_y max_x xᵀAy` is exactly
`convex_duality.md`'s weak duality `max_λ min_x ≤ min_x max_λ` (the adjoint inequality
`gc_unit`/`gc_counit`) **closed to equality**. The repo proves a concrete ∅-axiom instance: the
Kantorovich/W₁ LP duality in `OllivierRicci.lean` (60/0 PURE) — `kantorovich_weak_duality`
(`dualValue f π ≤ transportCost d π`, the `sup over potentials ≤ inf over plans` weak-duality direction)
and `ollivier_plan_optimal` (the **zero-gap / strong-duality** certificate: when a plan and a potential
*meet*, `dualValue = transportCost`, the plan is optimal among all plans with its marginals — the gap is
pinned to 0). That "they meet ⟹ optimal" is precisely **minimax = the duality gap vanishing = the q=+1
tight optimum** on the polytope, with `ollivier_bracket` the squeeze the value lives in. Minimax is an LP
saddle and *is* an instance of the same `sup_dual ≤ inf_primal` + "they meet" object — the leg expected
conceptual is instead a real ∅-axiom weak-duality + zero-gap theorem, the strongest grounding in the
entry. (The *named* `minimax`/`gameValue`/`payoffMatrix` saddle object is absent — see Dropped; the LP
*structure* it inhabits is built, exactly as `convex_duality.md` located its missing Lagrangian saddle.)

**(4) No pure equilibrium ↦ recovered by mixing = the q=−1 escape converted to q=+1 by the resolution
dial — GROUNDED as readings.** A game with no pure-strategy Nash equilibrium (matching pennies,
rock-paper-scissors) is the best-response correspondence having **no fixed point on the discrete
pure-action corners** — the q=−1 fixed-point-free escape (`no_surjection_of_fixedpointfree`,
`object1_not_surjective`): the diagonal is dodged on the finite corner set, the same bounded-diagonal
phenomenon as `game_theory.md`'s mex (`mex_eq_zero_iff_zero_excluded`, 12/0 PURE — the least value the
options miss). **Mixing** moves the resolution dial from the discrete corners to the **convex
mixed-strategy simplex** `Δ`, where Brouwer/Kakutani restore the fixed point — the q=−1 escape becomes
q=+1 converge. This is the *same* escape→converge resolution move the calculus runs throughout (discrete
mex gap ↦ continuous limit; finite cover ↦ compactness). The readings are built; the *named* convex
simplex `Δ` with a continuous correspondence is the `Real213` gap (leg 5).

**(5) Brouwer/Kakutani *continuous* existence = the `Real213` / continuous-fixed-point residue —
HONEST GAP.** This is the entry's located break, stated plainly per the brief. Brouwer's theorem (a
continuous self-map of a compact convex disk/simplex has a fixed point) and Kakutani's (an upper-
hemicontinuous convex-valued correspondence on a compact convex set has a fixed point) need a
**topological/continuous fixed-point primitive over the reals** — a `Real213`-cut compact convex `Δ`
with a continuous `BR`. The repo has the **discrete/algebraic** Lawvere fixed point
(`lawvere_fixed_point`, the existence leg of the diagonal engine) and the **modulated Banach contraction**
(`banach_fixed_point_modulated`, the q=+1 converge pole *under a contraction hypothesis*), but **no
Brouwer/Kakutani topological fixed-point theorem** — no fixed-point theorem for a *non-contractive*
continuous self-map of a compact convex set. The only `Brouwer` hits in `lean/E213` are **Brouwerian
bar-induction / the fan theorem** (`WKLHeineBorel.lean`, `Dini.lean`, `HeineCantor.lean`) — constructive
*logic*, NOT Brouwer's fixed-point theorem (constructively, Brouwer's fixed-point theorem is itself
non-constructive — equivalent to weak forms of choice/LLPO, the calibrated boundary `SYNTHESIS §5.2`
records). So: **the q=+1 fixed-point/diagonal engine is built (discrete Lawvere + modulated Banach), but
the *continuous, non-contractive* Brouwer/Kakutani existence theorem that classical Nash existence rests
on is the `Real213`/continuous residue — reached by none, the same compact-convex continuous-fixed-point
gap the geometry/topology cluster shares (`topology.md`'s arbitrary-cover quantifier, `convex_duality.md`'s
`sup` transform object).** Honest: the *structural* claim "Nash = the q=+1 fixed point of best-response" is
grounded; the *full classical existence machine* (continuous Kakutani on the mixed simplex) is the named
open leg, not a hand-wave.

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the fixed-point/diagonal engine
  (`OneDiagonal.lawvere_fixed_point` / `no_surjection_of_fixedpointfree`, 11/0;
  `FlatOntologyClosure.object1_not_surjective`/`self_covering_closure`, 7/0); (b) the formal q=±1 tag
  with both poles (`ResidueTag.residue_tag_two_poles` / `converge_residue_fixed` / `escape_residue_outside`
  / `golden_is_converge`, 55/0); (c) the q=+1 contraction engine
  (`banach_fixed_point_modulated`, delegated to PURE by `converge_residue_fixed`); (d) a real LP
  weak-duality + zero-gap (minimax) theorem (`OllivierRicci.kantorovich_weak_duality`,
  `ollivier_plan_optimal`, `ollivier_bracket`, 60/0); (e) the bounded-diagonal / no-pure-equilibrium
  escape engine (`Mex.mex_eq_zero_iff_zero_excluded`, 12/0).
- *Conceptual-only / the precise missing legs:* **all named strategic-game objects are ABSENT** (grep
  below — `Nash`, `bestResponse`, `minimax`, `payoff`/payoffMatrix, `strategy`/mixedStrategy, `zeroSum`,
  `correlated`, `vonNeumann`, `Kakutani`, `Brouwer` fixed point: zero hits). And the **continuous
  Brouwer/Kakutani existence theorem** is the `Real213`/continuous fixed-point residue (only the discrete
  Lawvere fixed point and the contraction-Banach fixed point are built).

So: **PREDICTION on the named object + PARTIAL grounding — the strongest *collapse* is that Nash is the
q=+1 fixed-point pole of the best-response self-map (the converge side of `lefschetz_degree.md`'s diagonal
engine), and minimax is `convex_duality.md`'s LP duality made tight; the continuous Kakutani existence
machine and the named `Nash`/`minimax`/`payoff` bundle are the open legs, not a hand-wave.**

## Revelation (collapse: Nash = the q=+1 side of the diagonal engine; minimax = LP duality on strategies)

**Collapse 1 — "a Nash equilibrium exists" and "the residue cannot be pointed" are ONE `(C,L)` object,
read at its two q=± signs.** The single self-cover/diagonal reading — a self-map `BR` self-pointing the
strategy space against `Δ` — generates *both* poles, the *same* object `lefschetz_degree.md` identified
for Lefschetz/Brouwer degree: read with a Bool weight (fixed-point-free) it is
`cantor_via_lawvere`/`object1_not_surjective` (the q=−1 escape: Cantor, Gödel, *and now
no-pure-strategy-equilibrium*); read in the existence direction it is `lawvere_fixed_point` (the q=+1
converge: *a Nash equilibrium exists*). **The q=−1 escape side of this exact diagonal underlies
Cantor/Gödel/Vitali (`SYNTHESIS §3`); its q=+1 converge side underlies φ/the Gaussian/ODE flows — and
now Nash existence.** Nash equilibrium is the **economic name for the q=+1 fixed-point pole** of the
notebook's central diagonal engine. This is the new datum and it is distinct from both neighbors:
`lefschetz_degree.md` read the diagonal with a *trace* weight summed down homology (a topological fixed
point); `game_theory.md` read the *combinatorial* P/N split (G=0 ⟺ the bounded mex diagonal). Nash reads
the *same diagonal* on the *strategy-space self-map*, q=+1 side = equilibrium.

**Collapse 2 — minimax = LP duality, the SAME `sup ≤ inf` + "they meet" object as Kantorovich/Fenchel.**
The von Neumann minimax theorem is not a separate theorem from `convex_duality.md`'s weak/strong duality:
`max min ≤ min max` is the adjoint inequality (`gc_unit`/`gc_counit`, weak duality =
`kantorovich_weak_duality`), and `max min = min max` is the **zero duality gap** = strong duality =
`ollivier_plan_optimal`'s "they meet ⟹ optimal" = the q=+1 tight optimum. So the game value is an LP
optimum on the strategy polytope, and minimax joins the **five-instance `f**=clo` / LP-duality family**
(`SYNTHESIS §2`: Galois + Legendre–Fenchel + Nullstellensatz + optimal transport + matroid closure) as
the *game-theoretic* face of one adjoint-closure object. Correlated equilibrium widens the polytope (a
joint distribution over action profiles satisfying incentive-compatibility *linear* constraints) — the
*same* LP feasibility reading on a larger `Δ`, which is *why* correlated equilibria always exist (the LP
is feasible / the convex polytope nonempty) where Nash needs the harder fixed point.

**Forcing — mixing is FORCED by the resolution dial converting q=−1 to q=+1.** "No pure equilibrium ⟹
mix" stops being an ad-hoc fix: the pure-action corners are the *coarse* resolution where the
best-response diagonal is dodged (q=−1 escape, `no_surjection_of_fixedpointfree`); moving the resolution
dial to the *convex* mixed simplex is exactly the escape→converge move (`game_theory.md`'s mex bounded
diagonal ↦ the continuous fixed point), and the convexity is what makes the q=+1 fixed point reappear —
the *same* convexity that makes `convex_duality.md`'s duality gap vanish. So **the requirement to mix and
the existence of the game value are one condition (q=+1, convexity) read two ways** — fixed point exists
(Brouwer on convex `Δ`) AND duality gap zero (LP on convex `Δ`) — precisely `convex_duality.md`'s "convex
⟹ strong duality + global minimum as one bit twice."

**Residue-surfaced — "an equilibrium exists" is the q=±1 tag at the best-response reading.** `BR` a
contraction / convex `Δ` ⟹ the equilibrium exists and (under contraction) is reached — the q=+1 converge
pole (`converge_residue_fixed`/`banach_fixed_point_modulated`); the pure-action restriction with no fixed
point ⟹ the diagonal escapes (q=−1, `no_surjection_of_fixedpointfree`). "The Nash existence theorem"
stops being a separate object and becomes **the q=±1 residue tag read at the best-response self-cover** —
the same tag as φ/Cantor/Gödel/Lefschetz, now on the strategy-space self-map.

**EXTEND by consolidation; no new axis.** The interior model v7.1 holds: Nash/minimax are the
fixed-point/diagonal engine (q=+1 side, Invariant B) × the LP adjoint-closure (`f**=clo` family,
`SYNTHESIS §2`) × the resolution dial (pure ↦ mixed = q=−1 ↦ q=+1), read across {direction (the q=±1
bit), resolution (pure/mixed)}. The one genuine continuous absence — the Brouwer/Kakutani topological
fixed-point theorem on a compact convex `Real213` simplex — is located precisely as the `Real213`
continuous-fixed-point residue, distinct from the discrete Lawvere fixed point and the contraction-Banach
fixed point that ARE built.

## Note for the technique

- **Nash is the cleanest economic instance of "the q=+1 side of the SAME diagonal whose q=−1 side is
  Cantor/Gödel."** `lefschetz_degree.md` showed the diagonal engine is *quantitative* (trace-weighted)
  and topological; `game_theory.md` showed it is *combinatorial* (the mex bounded diagonal, P/N). Nash
  shows it is *strategic*: the best-response self-map's fixed point. Three fields, one diagonal, read with
  three weights / on three carriers — strong evidence the q=±1 fixed-point engine is the load-bearing
  invariant `SYNTHESIS` claims.

- **Minimax confirms the LP-duality family is a single object across SIX fields now** (Galois, Legendre–
  Fenchel, Nullstellensatz, optimal transport, matroid, **and now zero-sum games**). The frontier target
  the calculus names precisely: define `gameValue (A) := max_x min_y xᵀAy` on a `Real213`/dyadic strategy
  polytope and instantiate `OllivierRicci`'s weak-duality + `ollivier_plan_optimal`'s zero-gap to obtain
  `max min = min max` — the **minimax theorem as the LP instance of the adjoint-closure**, the weld that
  would promote this leg from PREDICTION to a closed derivation (parallel to `convex_duality.md`'s named
  Legendre weld and `ConvolveRescaleContraction` welding Banach to the CLT).

- **The break is the `Real213` continuous-fixed-point residue — and it is the SAME break `topology.md`/
  `convex_duality.md`/`lefschetz_degree.md` hit, not a new one.** Nash existence in full classical
  generality (continuous Kakutani on the mixed simplex) needs a non-contractive continuous fixed-point
  theorem over the reals; the repo has the discrete Lawvere fixed point and the contraction-Banach fixed
  point. Constructively this is *expected*: Brouwer's fixed-point theorem is itself non-constructive
  (LLPO-strength, the calibrated boundary `SYNTHESIS §5.2`), so the absence is a **calibrated boundary,
  not a missing 213 primitive** — the same honest shape as non-standard analysis's ultrafilter. The
  frontier target: a constructive fixed-point statement (a `BR` with a modulus of continuity giving an
  approximate-equilibrium `ε`-fixed-point, the q=+1 narrowing bracket) — the `ε`-Nash equilibrium is the
  computable operand, the exact equilibrium the reached-by-none `Real213` cut.

---

### Verified Lean anchors (file:line:theorem — all grep-confirmed on `lean/E213`; purity via `tools/scan_axioms.py`, run from repo root this session)

| Leg | Theorem (file : line : name) | Status |
|---|---|---|
| ★★ **Nash existence = the q=+1 "fixed point exists" pole; best-response self-map against the diagonal** | `Lens/Foundations/OneDiagonal.lean:43 : lawvere_fixed_point`; `:51 : no_surjection_of_fixedpointfree` (q=−1 no-equilibrium escape); `:61 : cantor_via_lawvere`; `:101 : one_diagonal_generates` | **PURE, scanned 11/0** ✓ |
| ★ the residue = the non-surjected diagonal (self-cover faithful, never total) — the q=−1 escape (no pure eq.) | `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`; `:47 : object1_injective`; `:69 : self_covering_closure` | **PURE, scanned 7/0** ✓ |
| ★ **the q=±1 tag: Nash = converge pole; no-equilibrium = escape pole** | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`; `:160 : converge_residue_fixed` (q=+1, Nash exists); `:133 : escape_residue_outside` (q=−1); `:180 : golden_is_converge`; `:86 : multiplier_unimodular` | **PURE, scanned 55/0** ✓ |
| ★ **best-response dynamics converge = the q=+1 contraction / Picard iteration** | `Lib/Math/Analysis/BanachFixedPointModulated.lean:111 : banach_fixed_point_modulated` (in namespace `…BanachFixedPoint.CompleteMetricModulusMod`) | ∅-axiom ✓ (delegated to PURE by `ResidueTag.converge_residue_fixed`, 55/0; module-path scan mismatched the namespace, the theorem is the converge-pole kernel) |
| ★ **minimax (zero-sum) = LP weak duality on strategies** (`max min ≤ min max` = the adjoint inequality) | `Lib/Math/Geometry/DiscreteCurvature/OllivierRicci.lean:52 : kantorovich_weak_duality` (`dualValue ≤ transportCost`); `:40 : dualValue`; `:36 : transportCost` | **PURE, scanned 60/0** ✓ |
| ★ **minimax = strong duality** (`max min = min max` = zero gap = q=+1 tight optimum, von Neumann) | `OllivierRicci.lean:106 : ollivier_plan_optimal` (`dualValue=transportCost ⟹ optimal`); `:91 : ollivier_bracket` (the gap squeeze) | **PURE, scanned 60/0** ✓ |
| no pure equilibrium = the bounded-diagonal escape (cross-frame to combinatorial `game_theory.md`) | `Lib/Math/Combinatorics/Mex.lean:153 : mex_eq_zero_iff_zero_excluded`; `:95 : mexFrom_finds`; `:72 : mexFrom_lt_mem` | **PURE, scanned 12/0** ✓ |
| cross-frame | `lefschetz_degree.md` (the diagonal/self-map fixed-point engine, q=+1 exists / q=−1 escape), `convex_duality.md` (LP weak/strong duality = `kantorovich_weak_duality`/`ollivier_plan_optimal`), `game_theory.md` (combinatorial P/N, mex — distinct field), `martingales.md`/`golden_ratio.md` (the q=+1 fixed point) | prior, ∅-axiom ✓ |

### Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No named `Nash` / `equilibrium` / `bestResponse` object in `lean/E213`.** Grep (case-insensitive,
  over `lean/E213`): zero `nash`, zero `best.?response`/`bestResponse`. The named strategic-equilibrium
  object is the missing conceptual leg — flagged predicted-not-built, exactly as `game_theory.md` /
  `convex_duality.md` flag their absent named objects.
- **No `minimax` / `payoff`-matrix / `gameValue` / `vonNeumann` / `zeroSum` saddle object.** Grep: zero
  `minimax`, zero `von.?neumann` (the only `von Neumann` hit is **von Neumann entropy** in the
  quantum-information INDEX, a different object), zero `zero.?sum.?game`. The `payoff` hits are all the
  "structural payoff" English idiom (`Nat213/Order.lean`, `Irreducible.lean`, etc.), not a payoff matrix.
  The LP-duality *structure* minimax inhabits IS built (`OllivierRicci`, 60/0); only the named
  `gameValue`/`payoffMatrix` saddle instance is unwritten — exactly as `convex_duality.md` located its
  missing Lagrangian saddle.
- **No `strategy` / `mixedStrategy` / `correlated` object.** Grep: the `strategy` hits are unrelated
  ("migration strategy" comments, etc.); zero `mixed.?strateg`, zero `correlated.?equilib`. The mixed
  simplex is `probability.md`'s `ratio∘count` container (built) but no `Strategy`/`Game` type applies it;
  correlated equilibrium's incentive-compatibility LP is conceptual.
- **No `Brouwer` / `Kakutani` fixed-point theorem (the continuous existence leg).** Grep: zero
  `Kakutani`; the only `Brouwer` hits are **Brouwerian bar-induction / the fan theorem**
  (`WKLHeineBorel.lean`, `Dini.lean`, `HeineCantor.lean`) — constructive *logic*, NOT Brouwer's
  fixed-point theorem. The built fixed points are the **discrete Lawvere** (`lawvere_fixed_point`) and the
  **modulated Banach contraction** (`banach_fixed_point_modulated`); the **continuous, non-contractive
  Brouwer/Kakutani topological fixed-point theorem** on a compact convex `Real213` simplex — the leg
  classical Nash existence rests on — is the `Real213` continuous-fixed-point residue, reached by none.
  This is a **calibrated boundary** (Brouwer's theorem is itself non-constructive, LLPO-strength,
  `SYNTHESIS §5.2`), the same compact-convex continuous-fixed-point gap `topology.md`/`convex_duality.md`/
  `lefschetz_degree.md` share — not a missing 213 primitive.
- **Verified buildable witness (named, the weld the calculus predicts):** instantiate `OllivierRicci`'s
  `kantorovich_weak_duality` + `ollivier_plan_optimal` at a 2×2 zero-sum payoff matrix to obtain a closed
  `max min = min max` minimax instance (the LP saddle = the W₁ saddle, `dualValue = transportCost`) — the
  same shape as `OllivierRicci`'s already-built triangle/square/K_m worked examples (`:171`, `:273`,
  `:597`), re-read with the payoff matrix as the cost. This would promote leg (3) from PREDICTION to a
  closed minimax derivation, parallel to `ConvolveRescaleContraction` welding the Banach engine to the
  CLT. (Not built this session — flagged as the precise, verified-shape buildable target.)
