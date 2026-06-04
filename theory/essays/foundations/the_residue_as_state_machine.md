# The residue as a state machine — state read as state-transition

A cross-frame reading of `the_residue_as_primitive.md`, offered from the register-transfer
(RTL) frame.  It is a **Lens reading** (`seed/AXIOM/06_lens_readings.md`): not a claim that the
residue *is* a state machine, but that the self-pointing act, read through the automaton
dictionary, *is* the standard mathematics of state-based systems — because **coalgebras model
the mathematics of state machines**, and what `CoResidue` builds *reads as* a final coalgebra
(up to pointwise equality, among anti-reflexive coalgebras — `CoResidue.slashNu_final`; the
over-approximation `CoResidue.final_coalgebra` is for `F X = Bool × X × X`).  So the RTL
reading is a faithful operational facet of the construction — one Lens among others, not the
construction's identity.

## The point: state *read as* state-transition

In RTL one keeps the *register value* (state) and the *next-state logic* (transition) distinct.
The residue's fixed point is the place where they **coincide**: Lambek's iso `X ≅ F(X)` (the
forward decode `Lambek.decompose` together with the round-trip `Lambek.rebuild` — `build ∘
decode = id`) — the carrier is its own one-step decode.  `Lambek.decompose` reads a state's
transition (a halt-atom or a node branching to two next-states); `Lambek.rebuild` recovers the
state from it (lossless).  `StateMachine.state_transition_decode` packages it: every register value decodes to
a **terminal atom (halt, no successor)** or a **branch to two *distinct* next-states**, and is
terminal *iff* it is an atom.  The `x ≠ y` on the slash is, in this frame, the **non-degenerate
transition** condition — and that one fact propagates all the way to the νF carrier.

## The dictionary

| RTL / FSM | 213 / Lean |
|---|---|
| next-state logic `δ : X → (out, X, X)` | the coalgebra `c : X → Option Bool × X × X` (= `CoResidue.coOut`) |
| run the machine (seed → output trace) | the anamorphism `CoResidue.lAna` / `ana` |
| **determinacy** — behaviour fixed by the transition | finality `CoResidue.{lAna_unique, slashNu_final}` |
| terminal / halt state | an atom (peel-terminal, `Lambek.terminal_iff_atom`) |
| one clock tick = one transition | the count-Lens unit `1` (`MuNuMirror.ascent_adds_unit`) |
| reachable / terminating runs | **µF = Raw** (well-founded, every run halts at an atom) |
| trace / observable behaviour (infinite runs too) | **νF = `CoResidue.SlashNu`** |
| non-degenerate transition (distinct successors) | the slash's `x ≠ y` / `AntiRefl` |
| all-branch self-loop (successors identical), excluded | `allBranchL` (`∉ SlashNu`, since it requires `AntiRefl`) |
| free-running counter (state after `n` cycles) | `PrimitiveTower.rawTower` (`depth` = cycle count) |
| reachable state (built from an initial atom) | `StateMachine.BuildsIn` (`n`-step build relation) |
| behavioural / trace equivalence | `StateMachine.TraceEq` (`= ¬ Distinct`, no bisimulation) |
| reduced / minimised machine (no mergeable states) | `traceEq_finite_minimal` (trace map injective) |

## Determinacy = finality

The deepest RTL reading of `slashNu_final`: **fix the next-state logic, and the output trace
from any state is uniquely determined.**  `StateMachine.transition_determines_behaviour` states
it directly — any two behaviours `h`, `h'` that both implement the transition `c` agree at every
state and every trace (`∀ x p, h x p = h' x p`).  This is observational determinacy: two
implementations with the same transition relation produce the same observable behaviour.  It is
stated *pointwise* (the `h = h'` form would need `funext`) — the honest, ∅-axiom shape of
finality.

## Reachable vs trace semantics — and the residue between them

µF and νF are the two standard FSM semantics of one transition:

  - **µF (reachable-state semantics)** — `Raw`, the finite terminating runs: every descent
    halts at an atom (`Lambek.no_infinite_descent`, `isPart_wf`).  The synthesizable, bounded
    part.
  - **νF (trace semantics)** — `SlashNu`, the observable behaviours including the
    non-terminating ones.  The free-running, sequential part.

The free-running counter `rawTower` lives at their seam: read from µF it is an *unbounded
sequence of finite states* (`MuNuMirror.ascent_unbounded` — never a completed object,
`StateMachine.counter_no_return`: strictly increasing in `depth`, no state recurs); read from
νF it is *one* object, the trace `spineL` (`CoResidue.spineL_escapes` — outside every finite
Raw).  The **gap** between the two readings — that the trace `spineL` is no reachable finite
state — is exactly the **residue** (`FlatOntologyClosure.object1_not_surjective` at the
foundational scale; the un-enclosed face of `the_form_of_the_residue.md`).  So the µF/νF
distinction *reads as* the source-without-enclosure: reachable-out, trace-never-enclosed.

## The non-degenerate transition, end to end

A register that steps to two *identical* next-states is degenerate (a pure self-loop with no
information).  The slash forbids it (`x ≠ y`), and the forbidding propagates:

  - at µF: a branch decodes to two **distinct** next-states (`state_transition_decode`);
  - at νF: the all-branch self-loop `allBranchL` (both successors the same state, `coLeftAt
    = coRightAt`) is **excluded** — `StateMachine.self_loop_excluded`: `¬ AntiRefl allBranchL`,
    and since `SlashNu` requires `AntiRefl`, `allBranchL ∉ SlashNu`;
  - the *allowed* infinite machine is the counter `spineL` (each successor distinct from the
    last — `CoResidue.spineL_antiRefl`), not the self-loop.

So anti-reflexivity, the residue's `x ≠ y`, reads as **non-degeneracy of the transition**: the
νF carrier admits free-running counters but excludes pure self-loops.

## Reachability — every state is built from an initial state

The µF side has the standard FSM completeness property: **every state is reachable from an
initial (atom) state**, by a bounded number of build-steps.  The build relation
`StateMachine.BuildsIn n seed top` is the **`n`-step** iterate of the *reverse* peel
relation (`IsPart`, upward) — `refl` plus one-step `IsPart`-extension, not a transitive closure
(no `trans` is proved): each step builds a bigger register value from one of its constituents
(its next-state-down).

  - **The counter reaches every level on the clock.**  `StateMachine.counter_reachable`: from
    the reset atom `b`, the counter `rawTower n` is reached in *exactly* `n` build-steps —
    one rung per tick (`tower_ascent_isPart`).  With `rawTower_depth` it gives
    `counter_reaches_every_level`: the reached state has `depth = n`, so step-count = level.
    The counter is, in this reading, a **clock** — and (`counter_no_return`, §4) one that never
    revisits a state.
  - **Every state is reachable, within `depth` steps.**  `StateMachine.every_state_reachable`:
    for *any* register value `r` there is *an* atom `seed` (`a` or `b`, whichever floors that
    state — not a unique reset) and a step count `k ≤ r.depth` with `BuildsIn k seed r`.  The
    whole µF carrier is reachable from the atomic floor, and the build never takes more steps
    than the state's depth — `depth` is an *upper bound* on the build distance (`k ≤ r.depth`),
    not in general an equality.  (Proved by depth-bounded strong induction via `decompose`, the
    `isPart_wf` shape; no `Raw.rec`.)

So µF is not merely well-founded (descent terminates) but **reachable** (ascent from the atoms
covers it): the two faces of the same finite-build structure — read downward it converges
(`isPart_wf`), read upward it is generated from the initial states (`every_state_reachable`).

And the reachability bound is **tight**: `StateMachine.exact_descent` strengthens `k ≤ r.depth`
to an equality along the *deep spine* — every state reaches an atom in *exactly* `r.depth`
build-steps (`BuildsIn r.depth seed r`), each step dropping the depth by exactly the unit `1`
(descend into the `max`-realising child).  So `depth` *is* the deep-spine descent length, not
merely a bound on it.

## Behavioural equivalence — pointwise trace equality, the complement of `Distinct`

The standard FSM notion of *behavioural equivalence* (two states with the same observable
behaviour) here is `StateMachine.TraceEq s t := ∀ q, s q = t q` — agreement at every
observation path.  It is an equivalence relation (`traceEq_equivalence`), and the key fact is

  - `traceEq_iff_not_distinct` — **`TraceEq s t ↔ ¬ Distinct s t`**: behavioural equivalence is
    *exactly* the absence of a distinguishing observation.  The reverse direction uses only the
    **decidable** equality of `Option Bool` (`¬¬(s q = t q) → s q = t q`), **never** a
    coinductive bisimulation.

This is the operational payoff of the construction's design choice that inequality is
*positive*: `Distinct s t := ∃ q, s q ≠ t q` is a single witness path (`treeDiffPath`
constructs it), so its complement — behavioural equivalence — is the plain decidable negation.
Co-data equality is normally the hard, bisimulation-requiring direction; here it is free,
because the *inequality* carries the witness.

Two consequences read directly:

  - **The residue's `x ≠ y` is observable separation** — `slash_children_not_traceEq`: two
    distinct finite states embed as traces that are *not* trace-equivalent (the slash's
    disequality says the two next-states are observably different machines).
  - **Determinacy is trace equivalence** — `behaviours_traceEq`: any two implementations of the
    same transition `c` are trace-equivalent at every state (`transition_determines_behaviour`
    read through the equivalence relation — one class per state, both implementations in it).

## The finite machine is reduced (minimal)

The sharpest FSM-theoretic statement: the finite (µF) carrier is **reduced/minimal** — no two
distinct states are behaviourally equivalent, so trace equivalence coincides with state
equality.  (This is observational *faithfulness* — the trace map is injective; the right side
is structural identity, not an independently-defined contextual equivalence, so it is
minimality, not "full abstraction" in the denotational-semantics sense.)

  - `traceEq_finite_minimal` — **`TraceEq (lToShape t) (lToShape t') ↔ t = t'`**: two finite
    states are trace-equivalent iff they are the *same* state.  No two distinct finite states
    are behaviourally equivalent; there is no hidden behavioural collapse (no mergeable states).
    The non-trivial half is `CoResidue.lToShape_faithful` (distinct trees ⟹ distinct traces);
    the converse is reflexivity.
  - `raw_traceEq_iff_eq` lifts it to `Raw`: trace-equivalent register values are equal — the
    residue's finite carrier is observationally faithful.
  - `finite_states_finitely_separated` — and the separating observation is *finite*
    (`treeDiffPath` constructs the distinguishing experiment by structural recursion): two
    finite states never need an infinite observation to be told apart.

This is the finite-side counterpart of `spineL_escapes`: over µF, observation is *complete*
(state equality = trace equality, by a bounded experiment); the only behaviours that escape
finite observation are the genuinely infinite ones (`spineL`), which is exactly the residue's
un-enclosed face.

## Capstone: the µF carrier is reachable, reduced, deterministic

The readings above combine into one statement (`mu_carrier_reachable_reduced_machine`).  The
finite residue carrier, read as a state machine, satisfies *simultaneously* four properties:

  1. **total transition** — every state decodes to a halt-atom or a branch with two distinct
     next-states, terminal iff atomic (`state_transition_decode`, §1; defined for *all* states);
  2. **deterministic** — that decode is single-valued: no state is both atom and branch, so
     exactly one case applies (`transition_deterministic`, §1);
  3. **reachable** — every state is built from an initial atom within `depth` steps
     (`every_state_reachable`, §5);
  4. **reduced** — no two distinct states are behaviourally equivalent (`traceEq_finite_minimal`,
     §7): the trace map is injective.

Reachable + reduced is what *minimisation* produces — no unreachable states, no mergeable
states.  The **further** classical fact — that a reachable, reduced automaton is the *unique*
smallest machine with its behaviour, up to isomorphism (Myhill–Nerode) — is **not** formalised
here; only these four component properties are.  So the self-pointing act's finite carrier
*reads as* a reachable, reduced, deterministic machine: `Raw` reads not merely as *a* state
machine in this Lens but as a *minimised* one.  The infinite traces that escape this finite
carrier (`spineL`) are exactly the residue's un-enclosed face.

## The loop closes — one behaviour escapes the minimised machine

The finite machine of §8 is total, deterministic, reachable, and reduced — *complete on finite
behaviours*.  But the behaviour space strictly exceeds it (`residue_escapes_minimal_machine`):
the free-running counter trace `spineL` is

  - a **genuine non-degenerate behaviour** — `AntiRefl spineL` (distinct successors at every
    branch), so it inhabits the νF carrier `SlashNu`;
  - yet **not the trace of any finite state** — `spineL ≠ lToShape t` for every `t`
    (`spineL_escapes`).

So there is exactly such an escaping trace: the minimised finite machine is the canonical
*enclosure*, and the free-running trace is the *source* that no finite state encloses.  This is
`the_form_of_the_residue.md`'s **source-without-enclosure** read at the FSM scale — and the
µF/νF pair is not a dichotomy but the one self-pointing act read at its two cofinal ends
(reachable-out at the finite end, trace-never-enclosed at the infinite end).

## Open frontier (honest scope)

  - This is a *reading*, not an identity (`§6`, the facet discipline): the FSM vocabulary is one
    Lens; the residue is outside every view (`the_form_of_the_residue.md`).
  - Determinacy / finality is *up to pointwise/extensional equality* (`∀ x p`, not `funext`) and
    among *anti-reflexive* (non-degenerate) coalgebras — the honest scope of `slashNu_final`.
  - "Behavioural equivalence" here is *pointwise trace equality* (`TraceEq`, `∀ q`, not
    `funext`), **not** a coinductive bisimulation — `traceEq_iff_not_distinct` discharges it
    against the *positive* inequality `Distinct` via decidable `Option Bool` equality, so
    equality-by-bisimulation is never needed.

## Lean source

- `lean/E213/Theory/Raw/StateMachine.lean` (20 PURE) — the FSM-reading theorems above; in
  `Theory/Raw/API`.
- Reads `Theory/Raw/{Lambek, CoResidue, MuNuMirror, PrimitiveTower}` through the dictionary;
  companion to `the_residue_as_primitive.md`.

## How to verify

```bash
cd lean && lake build E213.Theory.Raw.API
python3 tools/scan_axioms.py E213.Theory.Raw.StateMachine
```
