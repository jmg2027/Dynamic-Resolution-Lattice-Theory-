# The residue as a state machine — state read as state-transition

A cross-frame reading of `the_residue_as_primitive.md`, offered from the register-transfer
(RTL) frame.  It is a **Lens reading** (`seed/AXIOM/06_lens_readings.md`): not a claim that the
residue *is* a state machine, but that the self-pointing act, read through the automaton
dictionary, *is* the standard mathematics of state-based systems — because **coalgebras are
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
distinction *is* the source-without-enclosure: reachable-out, trace-never-enclosed.

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

## Open frontier (honest scope)

  - This is a *reading*, not an identity (`§6`, the facet discipline): the FSM vocabulary is one
    Lens; the residue is outside every view (`the_form_of_the_residue.md`).
  - Determinacy / finality is *up to pointwise/extensional equality* (`∀ x p`, not `funext`) and
    among *anti-reflexive* (non-degenerate) coalgebras — the honest scope of `slashNu_final`.
  - "Behavioural equivalence" here is *pointwise trace equality*, **not** a coinductive
    bisimulation (the construction's whole point is that inequality is positive — `Distinct`,
    `treeDiffPath` — so equality-by-bisimulation is never needed).

## Lean source

- `lean/E213/Theory/Raw/StateMachine.lean` (5 PURE) — the FSM-reading theorems above; in
  `Theory/Raw/API`.
- Reads `Theory/Raw/{Lambek, CoResidue, MuNuMirror, PrimitiveTower}` through the dictionary;
  companion to `the_residue_as_primitive.md`.

## How to verify

```bash
cd lean && lake build E213.Theory.Raw.API
python3 tools/scan_axioms.py E213.Theory.Raw.StateMachine
```
