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

1. **Re-wire the three number-theory instances** as `descent_invariant`
   applications (`I = gcd / "vp-agree" / markovEq / Decomp`).  Each instance's
   local descent + invariant-preservation lemma is already proven; the task is
   to expose its step as an `R` and apply the schema, deleting the re-rolled
   fuel recursion.  Low-risk for vp/atomicity; see the subtlety for Markov.
2. **Markov permutation subtlety** (the one genuine open question before a
   clean 5-way unification).  Markov's `μ = max` descends only *after* re-sorting
   (`swap12/swap23`), so the step must be `jump ∘ sort` for `μ` to descend
   monotonically.  If that swap folds into a single relation `R` while keeping
   `μ` strictly monovariant, the unification is 5-way; if it cannot, Markov is a
   distinct *descent-up-to-permutation* schema and the union is only 4-way
   (gcd / Ricci / vp / atomicity).  **Check this before any promotion.**
3. **Promotion gate.**  `descent_invariant` is ∅-axiom and categorically the
   generator, but promotion (per `theory/PROMOTION_CRITERIA.md`) waits on the
   re-wirings landing (the instances *being* corollaries, not just claimed so).

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
