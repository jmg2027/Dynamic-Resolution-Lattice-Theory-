# The configuration lattice — event structure, the count formula, and the DRLT lattice

*Deep-research result (order theory / concurrency theory).  Classical scaffolding:
Newman 1942, Birkhoff 1937, Mazurkiewicz 1977, Nielsen–Plotkin–Winskel 1981,
Bombelli–Lee–Meyer–Sorkin 1987.  New combinatorial result: the order-ideal count
closed form, now ∅-axiom in `BipartiteDecomp/ConfigLatticeCount.lean`.*

## The object

The slash-cycle (each line → a point; each new point joins all not-yet-connected
points) is a confluent concurrent process.  Its reachable intermediate
configurations, ordered by inclusion, are the **order ideals of the operation
dependency poset** `P(V,s)` (V = vertices at cycle start, s = new points this
cycle), a **finite distributive lattice** — the configuration domain of the
corresponding conflict-free **Winskel event structure**.

## (1) Confluence ⟹ distributive lattice (the chain of classical theorems)

- **Newman's lemma** (1942): terminating + locally confluent ⟹ globally confluent.
  The cycle terminates per cycle (a fixed finite operation multiset) and is
  locally confluent (the only critical pairs are operations on distinct growth
  axes, which touch disjoint vertices and commute).  ⟹ Church–Rosser: every
  schedule reaches the same complete graph.
- **Birkhoff representation** (1937): the down-sets `J(P)` of a finite poset form a
  finite distributive lattice, and every finite distributive lattice is uniquely
  so (P = its join-irreducibles).  ⟹ the configuration lattice **is** a finite
  distributive lattice.

## (2) The precise classical framework — both, at two levels

- **Mazurkiewicz traces** (1977) = the *schedules*: alphabet Σ = operations,
  independence `I` = "act on disjoint axes"; a trace = an operation-sequence up to
  swapping adjacent independent events.  The session's "no global cycle / schedule
  independence" **is** trace equivalence.
- **Winskel event structures** (Nielsen–Plotkin–Winskel 1981) = the *states*:
  `(E, ≤, #)` with `E` = operations, `≤` = the dependency poset, `# = ∅`
  (conflict-free — every operation eventually fires).  Its configuration domain =
  consistent down-sets = `J(P)`; Winskel's theorem says this is prime algebraic =
  (finite case) a finite distributive lattice — **coinciding with Birkhoff**.

| 213 / DRLT phrase | concurrency object |
|---|---|
| growth axes | independent (commuting) events |
| operations on different axes commute | the independence relation `I` / trace `ab≡ba` |
| confluence (Conj. 2) | conflict-free + local confluence ⟹ Church–Rosser |
| no global cycle number | a trace is not a sequence; linear extensions non-canonical |
| intermediate states | event-structure configurations = order ideals `J(P)` |
| the lattice | prime algebraic configuration domain = finite distributive lattice |

§6.2 (operator=object, no external time) is the 213-native reason `I` is *forced*,
not chosen: no external clock ⟹ no canonical sequentialization ⟹ the invariant is
the trace / configuration domain, not any schedule.

## (3) The count — NEW closed form (∅-axiom)

`P(V,s)` has height 2: `s` minimal creations; for each, `V` private connection
atoms (one prerequisite); and `C(s,2)` cross atoms (two prerequisites).  Counting
order ideals by the "in" creation-set `S` (|S|=k):

> **I(V,s) = Σ_{k=0}^{s}  C(s,k) · 2^{V·k} · 2^{C(k,2)}.**

Verified: `I(2,1)=5`, `I(3,2)=145`, and **`I(5,7)=72 304 608 555 084 001`** (the
"vast" cycle-3 term, now exact).  Dominant term `k=s`: `I(V,s) ~ 2^{sV+C(s,2)}` =
`2^(edges added this cycle)`.  Now formalized PURE:
`BipartiteDecomp/ConfigLatticeCount.{cycle1,cycle2,cycle3,config_lattice_count_master}`
(`decide`, including the `2^56`-magnitude cycle-3 value).  The `2^{C(k,2)}` factor
is the Dedekind-number-flavoured ingredient, but the height-2/pairwise coupling
makes it *exactly summable* (a clean binomial sum, not an open enumeration).

## (4) Relativity — event structure, NOT causal set

Schedule-invariance = covariance: the causal partial order is invariant; "global
cycle = n" is a frame-dependent **antichain foliation** (a time function /
Cauchy-surface slicing); the only schedule-invariant grading is op-count rank,
whose level sets are antichains (never single states) — so a global cycle number
would require collapsing an antichain = choosing a frame.

But the object is a **Winskel event structure (prime algebraic domain), not a
causal set** (Bombelli–Lee–Meyer–Sorkin): a causal set is a bare locally-finite
order with no join/meet, no normal form, no conflict slot — it recovers geometry
only statistically.  The cycle has a genuine distributive lattice (join=union,
meet=intersection), a normal form (confluence → the complete graph), and a
present-but-empty conflict relation (the natural future home of §8 derivation
*failure*).  The causal poset is the event structure's *skeleton*; the extra
structure is exactly the lattice the theory is about.

## (5) This IS the "Lattice" of Dynamic Resolution Lattice theory

The limit `K_∞ ≡ point ≡ ∞` carries no internal distinction (§6.5); `MuNuMirror`
gives no completed νF object at finite resolution.  So **all content lives at
finite resolution** — the lattice `J(P)` of finite configurations is the only
non-trivial invariant the process produces.  "Dynamic **Resolution** Lattice"
reads literally: a *lattice* of *resolutions* (finite configurations) generated
*dynamically* (the confluent cycle), whose full-resolution limit collapses to the
structureless point.  It is the configuration-inclusion companion to the existing
observation-refinement lattice (`Lens/Lattice`, `Lens.refines`, PURE) — two
distributive lattices on Raw-native data justifying "Lattice" from both directions.

> **Cleanest statement.** The generative cycle is a conflict-free prime event
> structure with operation poset `P(V,s)`; by Newman it is confluent; by Birkhoff
> its configuration domain `J(P)` is a finite distributive lattice with
> `I(V,s) = Σ_k C(s,k)·2^{Vk}·2^{C(k,2)}` order ideals (= 5, 145,
> 72 304 608 555 084 001, …).  This configuration lattice — not the structureless
> limit `K_∞` — is the Dynamic Resolution Lattice; the absence of a canonical
> global cycle is the covariance (schedule-invariance) of its causal order.

*Scope (CLAUDE.md discipline).*  A math-branch structural identification
(primacy = rebuilding concurrency/order theory from the residue, boot §7.1), not a
physics falsifier; `K_∞ ≡ point` is the §6.5 pre-Lens reading, not an ∞-as-value
claim.

## Open

The full `confluence ⟹ distributive lattice` and the event-structure model are
not yet ∅-axiom (no rewriting/event-structure layer in Lean); only the *count*
`I(V,s)` is now formalized.  Building the event-structure / trace layer over Raw,
and connecting it to the existing `Lens/Lattice`, is the next target.
