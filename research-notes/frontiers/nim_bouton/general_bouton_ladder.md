# Frontier — general Nim / Bouton's theorem (nim-sum)

**Status**: OPEN.  **Tier**: 1.  Domain: combinatorial game theory.

## Closed

- **Subtraction game S={1,2}** — `Combinatorics/SubtractionGame.lean` (P = multiples of 3, 3-periodic).
- **Two-heap Nim** — `Combinatorics/NimTwoHeap.lean` (P = balanced `a=b`, the mirroring strategy, via the
  closed+progress P/N criterion, no game recursion, ∅-axiom).

## The target: Bouton (1901), general heaps

A Nim position `(h₁,…,hₖ)` is a P-position (player to move loses) **iff the nim-sum
`h₁ ⊕ … ⊕ hₖ = 0`** (`⊕` = bitwise XOR).  Two-heap is the `k=2` case (`a⊕b=0 ⟺ a=b`).

## Obstruction (measured)

Core `Nat.xor` lemmas are **`propext` + `Quot.sound`-dirty** (`Nat.xor_self`,
`Nat.xor_comm`, `Nat.zero_xor`, `Nat.xor_assoc` all checked dirty).  So Bouton
needs a **pure ∅-axiom XOR theory on `Nat`** first.

## Ladder

N1. **Pure nim-sum** — a ∅-axiom `Nat` XOR (bit-recursive or via a pure bit list)
    with `xor_self = 0`, `xor_comm`, `xor_assoc`, `zero_xor`, and the keystone
    `xor_eq_zero_iff : a ⊕ b = 0 ↔ a = b`.  Reusable infra (the repo's `BitFSM` /
    `Dyadic` bit machinery may seed it).
N2. **Closed direction (L1)** — nim-sum `= 0` ⟹ every single-heap reduction makes
    nim-sum `≠ 0`.  Reduces to `h ≠ h' ⟹ h ⊕ h' ≠ 0` (from N1's `xor_eq_zero_iff`)
    + nim-sum algebra (changing heap `h→h'` toggles the sum by `h⊕h'`).
N3. **Progress direction (L2, the hard one)** — nim-sum `s ≠ 0` ⟹ ∃ a heap with
    the highest set bit of `s`, reduce it to `h ⊕ s < h`, making nim-sum `0`.
    Needs the **highest-set-bit** analysis (`h ⊕ s < h` exactly when `s`'s top bit
    is set in `h`).
N4. **Bouton** — P-positions = `{nim-sum = 0}` via the closed+progress P/N
    criterion (same shape as `NimTwoHeap.nim_two_heap_P_positions`).

## Next action

N1 (pure `Nat`-XOR with `xor_eq_zero_iff`) — the gate; everything else reuses it.
