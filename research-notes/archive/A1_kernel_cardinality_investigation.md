# A1 — Lens-kernel cardinality: investigation log (2026-04-26)

## Problem

Open question from PAPER1 §5.4: uncountable lower bound on the
cardinality of the Lens-kernel space.

## Angles attempted

### A.1 leavesModNat-intersection family
For each f : Nat → Bool, define
  E_f := λ r r'. ∀ n, f n = false ∨
                       leavesModNat (n+2) view r = view r'.

**Observation**: E_f is a slash-congruence (intersection of
slash-congruences).

**Problem**: intersection of {leavesModNat m : m ∈ S} =
leavesModNat (lcm S).  Different S can give the same lcm
({2,3,6} and {6} both give lcm = 6).  → countable many
distinct kernels (one per natural number lcm).

### A.2 Function-space Lens via pointwise combine
For each f : Nat → Bool, define L_f : Lens (Nat → Bool) with
combine = pointwise xor (or ∧, ∨).

**Problem**: in the pointwise xor case, the kernel collapses to
the leaf parity Lens of (count_a mod 2, count_b mod 2) —
independent of f.  Pointwise ∧/∨: Raw collapses to 3 classes
{Raw.a, Raw.b, slash-stuff}, independent of f.

### A.3 f-dependent combine (if-then-else gate)
For each f, combine x y := if f n then x n ∧ y n else x n ∨ y n.

**Observation**: the kernel varies slightly depending on f (as
Raw.a, Raw.b and slash's view collapse to const-true/const-false
and f enters there).

**Problem**: most distinct f end up inducing the same partition.
No continuum separation.

## Conclusion (tentative)

All three angles hit a fundamental obstruction:

- Slash-compatibility forces a self-similar structure on the kernel —
  no channel for arbitrary f's information to leak into the kernel.
- Bool-valued fold-structured functions are themselves countable
  (BoolSqClassification: 4 classes × base values).
- Higher-codomain Lenses also have their view functions constrained
  to be fold-structured — that itself is countable many "shapes".

## Open status

- K may genuinely be countable (the fold-structured constraint on
  slash-congruences on Raw limits the degrees of freedom of partitions).
- Or a more sophisticated construction (e.g., distinct kernels in a
  higher-order Lens tower) may yield a continuum.

Next candidate attempts:
- **Recursive Lens^n α tower** (collapse already observed in
  LensOnLensImage — simple cases do not work).
- **Free combination of Sum/Product**: whether Lens (α × β) is a
  larger space than (Lens α) × (Lens β).
- **Cantor diagonalization ON the kernel space directly**:
  this can start carrying LEM-flavor, so risky.

## ROI assessment

Partial result (countable lower bound already in PAPER1 §5.4 +
KernelCardinalityLB).  A decisive proof or disproof of an uncountable
lower bound is a larger undertaking.

This note is a record of invested time + starting point for the next
attempt.  Status = open for the time being.
