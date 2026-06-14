# The universal descent schema — A6 FLOW widened to a reduction relation

**Origin:** multi-agent meta-analysis pass (corpus-wide proof-shape sweep,
continuation of `general_theory_metaanalysis.md`).  **Status:** general
generator **CLOSED ∅-axiom**; the instance re-wirings are the open seed.

## The finding (Finding H)

The A6 FLOW archetype (`Lib/Math/Foundations/MonovariantFlow.flow_reaches`) was
stated only for a **self-map** `f : X → X` and narrated as the discrete sibling
of geometric (Ricci) flow.  But the *same* fuel-recursion-on-a-monovariant is
re-proven, independently, in three number-theory domains that never import
`flow_reaches` or each other's descent machinery:

| instance | file | step `R` | monovariant `μ ↓` | invariant `I` | normal form |
|---|---|---|---|---|---|
| GCD flow | `MonovariantFlow.euclid_flow_normal_form` | `(a,b)↦(b%a,a)` | `fst` | `gcd213` | `(0,gcd)` |
| Ricci (discrete) | `GeometrizationConjecture/RicciFlowDiscrete.ricci_flow_reaches_normalized` | `spreadFlow` | curvature spread | round-state | constant curvature |
| UFD separation | `Meta/Nat/VpSeparation.vp_separation` | peel a prime `(m,n)↦(m/p,n/p)` | `m+n` | "valuations agree" | reconstruct `m=n` |
| Markov reachability | `…/Markov/MarkovUniqueness.markov_ordered_reachable` | Vieta jump `c↦3ab−c` + swap | `max=c` | `markovEq` | root `(1,1,1)` |
| atomic forcing | `Theory/Atomicity/Five.atomic_implies_five` | Bézout shift `(a,b)↦(a−3,b+2)` | bounded `a<3,b<2` | `Decomp n` | `(1,1)`, `n=5` |

Two features push past the self-map archetype: the step is a **reduction
relation** (carrier-changing / permuting, not one endo-`f`), and the answer is an
**invariant transported to the normal form**, not a bare fixed point.

## What closed (∅-axiom, `MonovariantFlow.lean`)

The common generator, all PURE (`tools/scan_axioms.py` → 18/18 pure):

- `Reaches R` — reflexive-transitive reachability under a step relation.
- `descent_reaches_fueled` / `descent_reaches` — a step relation `R` with a
  `Nat`-monovariant `μ` descending off a normal-form predicate `NF` reaches a
  normal form (constructive `Or`/`Exists` elimination; no `Classical`, no
  decidable equality on `X`).
- `reaches_invariant` — an `R`-step invariant is preserved along reachability.
- `descent_invariant` — **the headline**: the reached normal form carries any
  step-invariant `I` (`∃ y, NF y ∧ Reaches R x y ∧ I y = I x`).  *The answer is
  the invariant the descent preserves.*
- `flow_reaches_of_relation` — proves the **A6 self-map statement from the
  relation schema** (graph relation `fun a b => f a = b`, via `reaches_graph_iter`).
  So `flow_reaches` is literally subsumed: A6 FLOW is not a geometry instrument,
  it is the universal descent/normal-form lift.

## Open seed (the work)

1. **Re-wire the three number-theory instances** as schema applications.
   **Two landed this pass** (both PURE):
   - `MonovariantFlow.euclid_via_descent_invariant` — the GCD flow through the
     *invariant-carrying* `descent_invariant` (`I = gcd213`): the reached normal
     form carries the gcd.  Witness that the invariant schema (not just
     `flow_reaches`) reproduces the canonical result.
   - `Real213/Markov/MarkovDescentSchema` (`markov_descends_to_root`,
     `markov_descends_to_one`) — **the first genuinely relational (non-self-map)
     instance**: Markov's descent is `descent_reaches` on the nondeterministic
     `Down = Vieta-jump ∘ re-sort` relation; every ordered triple descends to the
     root `(1,1,1)`.  Reuses `markov_mid_lt_max` / `markov_partner_is_triple` /
     `markov_vieta_partner_le` etc.; the schema supplies the recursion.
   **Still open:** UFD separation (`vp_separation`) through the schema (moderate —
   the relation is inlined in a strong-induction-on-`m+n`; package `R` + fold the
   valuation-equality hypothesis into the carrier).
2. **Markov permutation subtlety — RESOLVED (the fold is clean, 5-way confirmed).**
   `μ = max` is *permutation-invariant*, so the re-sort (a permutation of the
   triple) does not change `μ`, and the Vieta jump strictly drops it
   (`markov_mid_lt_max : b < c` + the sorted target's max is `b`).  The bundled
   `Down = jump ∘ sort` therefore strictly descends in the *same* schema — no
   quotient-by-symmetry.  Constructively branched (`Nat.lt_or_ge`, no `Classical`).
   Witnessed end-to-end by the PURE `MarkovDescentSchema` above.
3. **Honest nuance — atomicity is a *degenerate* member, not a genuine iterated
   descent.**  `atomic_implies_five` uses a *single* bounded Bézout shift as a
   contradiction generator (`μ = a` bounded `< 3`), not an iteration to a fixed
   point; it fits the schema's *shape* (`μ`/`NF`/invariant) but not its *spirit*,
   so re-expressing it buys little (it would be a re-proof).  The clean unification
   is therefore **4 iterated descents (GCD / Ricci / UFD / Markov)** + atomicity as
   a boundary single-step case — recorded plainly, not inflated to "5 instances".
4. **`propext` caveat for Prop-invariants.**  Carrying a *Prop* invariant (markovEq,
   coprimality) through `descent_invariant`'s `I y = I x` needs `propext` (equality
   of `Prop`s) — forbidden.  So Markov's coprimality reproduction stays the
   *reachability* (`descent_reaches`, no `I`) plus the existing up-direction
   `markov_reachable_coprime`; only `Nat`/data-valued invariants (gcd) ride
   `descent_invariant` cleanly.
5. **Promotion gate.**  `descent_invariant` is ∅-axiom and categorically the
   generator; with the GCD + Markov instances landed and UFD the one remaining,
   promotion (per `theory/PROMOTION_CRITERIA.md`) is within reach once UFD lands.

## Resonance — LOOP/FLOW and the residue unit (honestly: a confirmation, not a new unification)

The descent schema (FLOW, well-founded descent) and the **operation/number
tower** (`simplicial_operation_tower.md`, built by forward iteration = LOOP /
ascent) are the two directions of the *same* `Nat`-recursion generator — the
LOOP/FLOW dual the `MonovariantFlow` header already names.  In descent, `μ`
strictly decreases **by a unit** each step (`< `, i.e. `≥ +1`); in ascent, each
rung adds **one** DOF / one transport-rung gap (`pow_twist_is_one_rung_shear`,
`DOF = rung − 2`).  Both are the residue unit `1` (the odometer `+1`,
`the_residue_unit_odometer.md`) read in the two dual directions — descent floor
vs ascent rung.  Per the shared-generator criterion (`boundary_discipline.md`)
this is an **instance** of the already-promoted "`iter` is the β-unification
site," not a new unification — recorded as a confirming cross-direction
resonance, tagged so it is not inflated.
