# 213-native Euclidean division

**Status**: Closed.

## Why a native version

Core Lean's `Nat.div` / `Nat.mod` lemmas carry `propext` (several also
`Quot.sound`).  The repo's ∅-axiom replacement for the **operator** facts
(`a*b/a = b`, `(a + b·c)/c = …`, mod variants) is
`lean/E213/Meta/Nat/NatDiv213.lean` — strict-∅-axiom code that needs a `/`
or `%` lemma uses it (e.g. `KerSizeUniversal` decodes the flat edge index
`Fin (c·NS·NT)` with it to prove the universal δ⁰-kernel = constants on
the canonical flat coboundary).

This Euclidean-division file is the **relational** complement: it
characterises division as the relation `IsQuotRem d n q r` (existence +
uniqueness), built by **upward** induction from ∅-axiom `Nat`
arithmetic — convenient where the spec, not the `/` operator, is consumed.

## Content

`lean/E213/Lib/Math/NumberTheory/EuclideanDivision.lean` (∅-axiom):

  - `exists_quot_rem` — for `d > 0`, every `n` factors as `n = d·q + r`
    with `r < d`.  Ordinary induction on `n`: each step increments the
    remainder, rolling over to the next quotient when it would reach `d`.
    No subtraction, no core `Nat.div`.
  - `quot_rem_unique` — the `(q, r)` is unique.  Induction on the first
    quotient; the cross cases force a remainder `≥ d`, contradicting
    `r < d`.  Uses a local ∅-axiom right-cancellation
    (`add_right_cancel_pure`, since core `Nat.add_right_cancel` carries
    `propext`).
  - `euclidean_division` — existence + uniqueness packaged: for `d > 0`
    and every `n` a unique `(q, r)` with `n = d·q + r`, `r < d`.

This characterises Euclidean division as a relation (`IsQuotRem`),
∅-axiom, without ever unfolding core `Nat.div`.

## Scope

This is the division *characterisation* (existence + uniqueness).  It
does **not** re-derive facts about Lean's `/` operator — connecting the
native relation to core `Nat.div` would require core division lemmas and
re-import `propext`.  Downstream ∅-axiom code that needs a division fact
takes it from `IsQuotRem` / `euclidean_division` directly.

## Connection

- `theory/math/combinatorics/graph_connectivity.md` — companion native
  infrastructure (graph-connectedness induction), same ∅-axiom-by-design
  motivation
- `lean/E213/Lib/Math/Combinatorics/Pigeonhole.lean` — same pattern: a
  core-lemma route forced `propext`, replaced by explicit ∅-axiom `Nat.*`
  reasoning
