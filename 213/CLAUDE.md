# CLAUDE.md — 213 sub-project

## Scope

`213/` develops a minimalist formal framework (Raw + Lens) in
Lean 4 core (Mathlib-free).  It is the foundational companion
to DRLT: same axiom philosophy (*"things exist with pairwise
relations"*) at the purely mathematical / foundational layer.

**Single source of truth for philosophy**: this file + the
four files it points to.  Every session MUST read them before
acting.

## DO NOT (session-level traps — cost ~1 h per violation)

These are mistakes Claude tends to make by training bias.
Each one has already wasted at least one session.  Do **not**
repeat them.

1. **Do not call Lens a functor.**
   Lens is **pre-categorical**.  Functor presupposes a
   category on both sides; Raw has no morphisms and no
   category structure.  Calling Lens a functor silently
   imports category theory as a prior — breaks the whole
   framing.  See `notes/19_lens_not_functor.md`.
   - OK: "Lens", "observation", "view", "catamorphism-style
     extraction", "fold".
   - NOT OK: "functor", "morphism in **Cat**", "preserves
     structure".

2. **Do not read `{a, b, /}` as a ZFC set.**
   The Raw axiom is not "three set elements".  It is a
   generation rule: two primitive distinctions (written `a`
   and `b` for convenience) and a binary pairing rule
   (written `/`).  Braces, commas, and the `∈` symbol carry
   ZFC baggage that the Raw axiom does not assume.
   See `NOTATION.md` for the full convention.

3. **Do not assume Raw's elements "already exist" or
   "are being generated".**
   The axiom does not judge existence mode.  Both the
   Platonic ("all terms are already there") and
   constructive ("terms are built one step at a time")
   readings are consistent with the axiom and with every
   Σ-theorem in `Infinity/`.  The distinction itself is a
   Lens output.  "Don't care" is not sloppiness — it is a
   **meta-theorem** about the axiom.
   See `notes/17_existence_mode_lens.md`.

4. **Do not treat cardinality as a property of Raw.**
   Cardinality is a property of `(Raw, Lens)` pairs.
   Raw itself carries no cardinality until a Lens is
   chosen.  "Is Raw countable?" is ill-posed at the axiom
   level; it becomes well-posed only after pairing Raw
   with a specific Lens.  See `Infinity/` Σ-series and
   `notes/12_r5b_reframing.md`.

## DO (orientation)

- **DRLT axiom `G_ij = ⟨ψ_i|ψ_j⟩` is the complete-graph
  K_n presentation of the Raw axiom.**  Same content,
  different (geometrically natural) encoding.  213 and
  DRLT physics are two Lens outputs of the same core.
  See `notes/18_complete_graph_lens_base.md`.

- **Lens catalogue is bridge-search infrastructure.**
  The R1–R5 profile + comm/assoc/alt/flex axes form a
  quantitative index; two mathematical domains are
  connectable via Lens-meet.  See
  `notes/20_bridge_search_infrastructure.md`.

- **Mathlib-free enforcement.**  `lake build` succeeds
  from Lean 4 core (`leanprover/lean4:v4.16.0`).  This is
  not aesthetic; it prevents external math from smuggling
  into Raw's self-containedness.

## File map (load in this order at session start)

| # | File | Purpose |
|---|------|---------|
| 1 | `CLAUDE.md` (this) | DO/DO-NOT + pointers |
| 2 | `NOTATION.md` | notation conventions (ZFC-free) |
| 3 | `research/infinity-as-lens/CLAUDE.md` | track scope |
| 4 | `research/infinity-as-lens/HANDOFF.md` | current state |
| 5 | `notes/17–20` (new) | philosophy consolidation |
| 6 | root `HANDOFF.md` | session arc continuity |

## Authors & licence

- **Author: Mingu Jeong only.**  Claude in Acknowledgments.
- 0 sorry, 0 external axioms beyond the one stated.
- Lean 4 core only — no Mathlib.
