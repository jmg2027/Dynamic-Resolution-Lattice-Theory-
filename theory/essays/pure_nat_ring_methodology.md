# PURE Nat ring methodology — closing ∀n identities in ∅-axiom Lean

How does a strict-PURE codebase (no Mathlib, no propext, no Quot.sound,
no Classical) prove universal polynomial identities over ℕ or ℤ?  The
answer that emerged from the P-orbit closure programme is a small
**213-PURE Nat ring toolkit** (`Lib/Math/NatRing.lean`) plus a
**Nat-additive reformulation pattern** that sidesteps Int.

This essay distils the discovery and the pattern, applied first to the
universal Cassini identity for the Pell-Lucas trace orbit, then to
`det(P^n) = 1` (Fibonacci Cassini at even indices).

## The blocker

Concretely, Lean 4 core proves these standard identities — but each
of them carries `propext` (and sometimes `Quot.sound`) through its
proof skeleton:

| Lean core lemma | Identity | Axioms |
|---|---|---|
| `Int.add_comm` | `a + b = b + a` | propext |
| `Int.mul_comm` | `a * b = b * a` | propext |
| `Int.sub_sub` | `a - b - c = a - (b + c)` | propext |
| `Int.mul_sub` | `a * (b - c) = a*b - a*c` | propext |
| `Nat.mul_assoc` | `a * b * c = a * (b * c)` | propext |
| `Nat.add_mul` | `(a + b) * c = a*c + b*c` | propext |
| `Nat.add_right_cancel` | `a + b = c + b → a = c` | propext |
| `Nat.sub_add_cancel` | `b ≤ a → a - b + b = a` | propext |
| `Nat.le_of_add_le_add_right` | `a + b ≤ c + b → a ≤ c` | propext |

The 213 axiom standard requires `#print axioms ↦ "does not depend on
any axioms"`.  Any DIRTY theorem counts as `sorry`-equivalent and
does not contribute to the DRLT Validation Standard.

Therefore: induction-based proofs of universal polynomial identities
over ℤ or ℕ in PURE Lean are blocked at every meaningful step — by
the very lemmas the proof needs.

## The two-part fix

### Part 1 — Re-derive the toolkit PURELY

Each of the propext-leaking lemmas above is **structurally provable**
without propext, by direct recursion on the natural-number argument
using `Nat.succ.inj` (which IS PURE).  Examples:

```
theorem nat_mul_assoc : ∀ (a b c : Nat), a * b * c = a * (b * c)
  | _, _, 0     => by rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | a, b, c + 1 => by
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, nat_mul_assoc a b c]

theorem nat_add_right_cancel : ∀ {a b c : Nat}, a + b = c + b → a = c
  | _, 0,     _, h => h
  | _, _ + 1, _, h => nat_add_right_cancel (Nat.succ.inj h)

theorem nat_sub_add_cancel : ∀ {a b : Nat}, b ≤ a → a - b + b = a
  | _, 0,     _ => by rw [Nat.sub_zero, Nat.add_zero]
  | 0, _ + 1, h => absurd h (by intro hf; cases hf)
  | a + 1, b + 1, h => by
    have hb : b ≤ a := Nat.le_of_succ_le_succ h
    rw [Nat.succ_sub_succ, Nat.add_succ, nat_sub_add_cancel hb]
```

These verify `#print axioms` empty — they are 213-PURE.  The PURE
Nat ring toolkit lives at `lean/E213/Lib/Math/NatRing.lean` and
provides:

  `nat_mul_assoc, nat_add_mul, nat_add_right_cancel,
   nat_add_left_cancel, nat_sub_add_cancel, nat_add_sub_self_right,
   nat_le_of_add_le_add_right, nat_swap_left_mul,
   three_mul_eq, two_mul_eq`.

Every Nat ring manipulation can be expressed via these primitives
combined with the PURE-core lemmas (`Nat.add_comm`, `Nat.mul_comm`,
`Nat.add_assoc`, `Nat.mul_add`, `Nat.add_right_comm`).

### Part 2 — Nat-additive reformulation

Int polynomial identities can be rephrased over Nat **provided the
identity carries no negative term**.  The standard tactic:

  `a - b = c`  ↔  `a = c + b`  (Nat-additive form)

For the Lucas-Pell Cassini identity

  `L(n) · L(n+2) − L(n+1)² = d`

the Nat-additive form is

  `L(n) · L(n+2) = L(n+1)² + d`.

Both sides are positive, so the identity holds verbatim in ℕ
provided `Lnat : Nat → Nat` mirrors the Int-valued `L : Nat → Int`
at every non-negative index.

The Lnat sequence is defined via the **truncated-Nat recurrence**:

  `Lnat (n+2) = 3 · Lnat (n+1) - Lnat n`     (Nat subtraction)

This needs `Lnat n ≤ 3 · Lnat (n+1)`, which follows from the
monotonicity `Lnat n ≤ Lnat (n+1)` — itself proved jointly with
the **additive recurrence**

  `Lnat (n+2) + Lnat n = 3 · Lnat (n+1)`

by *joint induction* (one invariant of the two coupled statements,
proved together so each step has access to both IHs).

## The universal Cassini proof

With the joint mono+add recurrence in hand, the universal Cassini
identity follows by direct induction:

  **Base** (n = 0):  `Lnat 0 · Lnat 2 = 2·7 = 14 = 9 + 5 = Lnat 1² + 5`. `decide`.

  **Step**: assume `Lnat k · Lnat (k+2) = Lnat (k+1)² + 5`.  Show
  the same at `k+1`.  Equate the two sides plus `Lnat(k+1)²` on
  each:

```
  Lnat(k+1) · Lnat(k+3) + Lnat(k+1)²
    = Lnat(k+1) · (Lnat(k+3) + Lnat(k+1))         [mul_add]
    = Lnat(k+1) · (3 · Lnat(k+2))                  [add_recurrence at k+1]
    = 3 · Lnat(k+1) · Lnat(k+2)                    [nat_swap_left_mul]
    = (Lnat(k+2) + Lnat k) · Lnat(k+2)             [add_recurrence at k, reversed]
    = Lnat(k+2)² + Lnat k · Lnat(k+2)              [nat_add_mul]
    = Lnat(k+2)² + (Lnat(k+1)² + 5)                [IH]
    = (Lnat(k+2)² + 5) + Lnat(k+1)²                [add_right_comm + assoc]
```

Cancel `Lnat(k+1)²` from both sides via `nat_add_right_cancel`.
Done.

Every step uses only `NatRing` primitives plus PURE-core `Nat.mul_add`
and `Nat.add_right_comm` — no Int, no propext.

## The det(P^n) = 1 proof

A second universal identity closes via the same pattern.  The matrix
entries of `P^n` satisfy 1-step recurrences

  `Q00 (n+1) = 2 · Q00 n + Q01 n`
  `Q01 (n+1) = Q00 n + Q01 n`
  `Q11 (n+1) = Q00 n`             (matrix symmetry: `Q00 = Q01 + Q11`)

with seeds `Q00 0 = 1, Q01 0 = 0, Q11 0 = 1`.  These avoid Nat
subtraction entirely.  The universal statement

  `Q00 n · Q11 n = Q01 n² + 1`         (Fibonacci Cassini, even index)

is then proved by induction on `n` with the **IH-driven polynomial
helper**

  `Q00² = Q00 · Q01 + (Q01² + 1)`     [derived from IH + Q00 = Q01 + Q11]

substituted once into the LHS expansion of the (k+1) goal, then
closed by additive-commutative normalisation using the NatRing
primitives.

## The closure pattern

The recipe generalises to any universal identity over a PURE Nat
sequence with bounded subtraction:

  1. **Reformulate the identity in Nat-additive form** — move all
     negatives to the other side so both sides are Nat-positive.

  2. **Define the sequence(s) in PURE Nat** — either via truncated
     subtraction (requires monotonicity to be safe) or via shifted
     recurrences without subtraction.

  3. **Establish monotonicity and additive recurrences jointly** —
     joint induction couples invariants whose individual proofs
     would otherwise be circular.

  4. **Apply the identity by induction**, using:
     - PURE `Nat.add_comm`, `Nat.mul_comm`, `Nat.add_assoc`,
       `Nat.add_right_comm`, `Nat.mul_add` (already PURE in core);
     - PURE `nat_mul_assoc`, `nat_add_mul`, `nat_add_right_cancel`,
       `nat_sub_add_cancel`, `nat_le_of_add_le_add_right`
       (re-derived in `NatRing`);
     - IH-driven helpers that substitute the inductive hypothesis
       at one targeted position (often via a `rw [show ... from ...]`
       block to position the substitution).

  5. **Bridge to the Int form** by exhibiting `Lnat n = (L n).toNat`
     (or equivalent) at concrete indices via `decide`.  The
     concrete bridge plus the universal Nat statement transports
     the result to ℤ when needed.

## Why this is non-trivial

Without Mathlib's `ring`, `omega`, `linarith`, `nlinarith`,
`polyrith`, `decide` macros, etc., universal polynomial identities
over ℤ are genuinely hard in PURE Lean.  The blocker is not the
proof complexity — Cassini induction is a textbook one-liner with
`ring` — but the axiom hygiene: Int polynomial commutativity and
distributivity in Lean core all leak `propext`.

The Nat-additive workaround is small enough to be readable and
big enough to handle the universal identities the P-orbit closure
programme needed.  It is the 213-native answer to "how do you do
universal algebra without `ring`?"

## Applications closed so far

| Theorem | Lean module | PURE |
|---|---|---|
| `cassini_universal : ∀ n, Lnat n · Lnat(n+2) = Lnat(n+1)² + 5` | `Px/CassiniUniversal` | ✓ |
| `det_pn_universal : ∀ n, Q00 n · Q11 n = Q01 n² + 1` | `Px/PnFibonacciUniversal` | ✓ |

## Applications open

The same pattern unblocks the following deferred frontiers:

  · **Universal `P^n` entry formula**: `Q00 n = fib(2n+1)`,
    `Q01 n = fib(2n)`, `Q11 n = fib(2n-1)` ∀n.  Inductive proof
    matching the matrix recurrence with the Fibonacci recurrence.

  · **Universal Cassini for arbitrary 2nd-order Pell sequences**:
    abstract `(P, Q)` Pell-Lucas pairs with `αβ = Q = 1`, `α+β = P`,
    discriminant `D = P² − 4Q`.  Generalises `cassini_universal`.

  · **Universal `trace(P^n) = L(n)`**: connecting the Lnat sequence
    to the matrix-entry sum `Q00 n + Q11 n`.  Inductive matching of
    additive recurrences.

The NatRing toolkit is the structural enabler; each application
is a finite extension of the toolkit + a Nat-additive induction.

## Lean source

  · `lean/E213/Lib/Math/NatRing.lean` (10 PURE)
  · `lean/E213/Lib/Math/Mobius213/Px/CassiniUniversal.lean` (16 PURE)
  · `lean/E213/Lib/Math/Mobius213/Px/PnFibonacciUniversal.lean` (14 PURE)

## Cross-references

  · `theory/math/mobius213_p_orbit_closure.md` — the chapter; the
    universal closures are listed under "Closure status".
  · `theory/essays/p_orbit_closure_master.md` — 11-phase marathon
    synthesis; this essay closes two of its three remaining
    frontiers.
  · `theory/essays/pure_funext_avoidance.md` — companion essay on
    avoiding `funext` in PURE Lean (similar discipline at a
    different layer).
