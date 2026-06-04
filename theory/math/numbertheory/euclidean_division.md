# 213-native Euclidean division

**Status**: Closed.

## Why a native version

Core Lean defines `Nat.div` / `Nat.mod` by well-founded recursion, and
**every** core lemma about them carries `propext` (several also
`Quot.sound`) — probe-verified across `Nat.mul_div_cancel`,
`Nat.add_mul_div_left/right`, `Nat.mul_add_div`,
`Nat.add_mul_mod_self_left`, `Nat.div_one`, and the subtraction lemmas
`Nat.sub_add_cancel`, `Nat.add_sub_cancel'`.  Any strict-∅-axiom 213
development that reasons about `/` or `%` through those lemmas loses its
purity.

So division-based combinatorics in 213 takes the division facts from a
native primitive built the other way — by **upward** induction, using
only ∅-axiom `Nat` addition / multiplication / order lemmas.

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
