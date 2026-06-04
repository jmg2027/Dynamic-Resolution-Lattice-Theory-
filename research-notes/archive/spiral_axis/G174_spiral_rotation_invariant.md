# G174 — the spiral rotation invariant: the golden form conserved at every turn

**Date**: 2026-06-02.  **Status**: closed ∅-axiom result (deep-research follow-through).
**Source of truth**: `lean/E213/Lib/Math/Real213/SpiralRotationInvariant.lean` (3 PURE).
**Anchors**: `Real213/ProbeTwistConic` (`Q_preserved`), `Real213/Mobius213Equiv`
(`Pstep`, `Pseq`), `Real213/Mobius213PellInvariant` (`Pseq_seedZero_pell_invariant`, the
`N=−1` template), `Meta/Tactic/NatHelper` (`add_right_cancel`, pure).

## The question (the "self-similar spiral" intuition, formalized)

The intuition: the framework's expansion is one self-applying operation recurring at every
scale — a *self-similar spiral*, not an infinite regress.  Two readings of it: the residue
side (`DepthHeightDiagonal.diag_self_applies` — the diagonal applies to its own output) and
the **atomic** side — the `P = [[2,1],[1,1]]` orbit (Pell/Fibonacci convergents spiralling
to φ).  A deep-repo survey found the atomic side's missing brick: `Q_preserved` proves the
golden form `Q(m,k) = m²−mk−k²` is conserved by **one** `Pstep`, but iterated preservation
(the invariant at *every* turn) was not formalized.  That iterated invariant is the literal
"spiral rotation invariant" of the originating proposal.

## What is now closed

`SpiralRotationInvariant` iterates the one-step law:

  - `add_cancel_chain` (pure, additive) — the transitivity of hyperbola membership: if
    `(a,b)` is on `(m,k)`'s `Q`-hyperbola and `Pstep (a,b)` is on `(a,b)`'s, then
    `Pstep (a,b)` is on `(m,k)`'s.  Proved by adding the two sign-free equations and
    cancelling the common `ab+bb` (`NatHelper.add_right_cancel`; the Lean-core
    `Nat.add_right_cancel` is propext-dirty).
  - `qinv_step` — one turn preserves `(m,k)`-membership (`Q_preserved a b` + the chain).
  - ★★★ `Q_iterate_preserved` — for **every** `n`, `Q(Pseq (m,k) n) = Q(m,k)`, sign-free:
    `(Pseq (m,k) n).1² + mk + k² = (Pseq (m,k) n).1·(Pseq (m,k) n).2 + (Pseq (m,k) n).2² + m²`.
    Induction on `n` (base = seed membership by additive comm; step = `qinv_step`).

So the convergent orbit stays on its own hyperbola `Q = N` as the spiral turns: the golden
form (disc `5 = NS+NT`) is the **rotation invariant**, preserved identically at every scale
of the self-similar `P`-shift.  The same shape as `Pseq_seedZero_pell_invariant` (which
pinned the `N=−1` orbit); this generalises it to every `(m,k)`/`N`.

## Reading: the two spirals, one mechanism

The self-similar spiral has two faces, both now ∅-axiom:

  - **atomic / frozen-form** (this note): the `P`-shift is the same step at every turn
    (`Pseq` iterates one `Pstep`), and the golden `Q` is conserved at every turn
    (`Q_iterate_preserved`) — same operation, same invariant, every scale;
  - **residue / open-end** (`DepthHeightDiagonal`): naming the whole tower escapes it
    (`height_diagonal_escapes`), and the diagonalisation applies to its own output
    (`diag_self_applies`) — same operation, every meta-level, always a residue.

The atomic spiral *conserves* a form (bounded, recurrent — the hyperbolic golden orbit);
the residue spiral *escapes* (unbounded, open — the ceiling/ε₀ direction).  Both are the
*same* self-applying mechanism read at the floor (det-one `P`, where the form is conserved)
and at the ceiling (the residue, where naming escapes) — the two ends the `5`-floor
unification (`FiveFloorUnification`) ties together.

## Open

  - The convergence/attraction of the spiral to φ (the iteration *limit*) is the
    real-analysis reading (rate of approach), on the real-number track — not pinned here.
  - A single statement uniting the atomic conservation and the residue escape as one
    operator's two regimes (bounded vs unbounded) — a synthesis, not yet a theorem.
