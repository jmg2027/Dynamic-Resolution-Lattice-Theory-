import E213.Lib.Math.Real213.Core.CutPoset

/-!
# Mobius213Equiv — Möbius P-orbit equivalence on cuts

The 213 Möbius matrix P = [[2,1],[1,1]] acts on (m, k) ↦
(2m+k, m+k).  Iterating P from the two natural seeds yields
two convergent chains:

  · seed (0, 1): orbit (0,1), (1,1), (3,2), (8,5), (21,13), ...
  · seed (1, 0): orbit (1,0), (2,1), (5,3), (13,8), (34,21), ...

These coincide (shifted) with `P_numerator` / `P_denominator`
from `Lib/Math/Mobius213.lean` — the same Fibonacci-even/odd
Pell convergents whose ratios approach φ² and 1/φ².  The matrix
is internal to 213: trace = NS, det = 1, disc = NS+NT = d,
eigenvalues φ², 1/φ².

## What this file delivers

  · `Pstep`, `Pseq` — P-iteration on Nat × Nat
  · `seedZero := (0, 1)`, `seedInf := (1, 0)` — the two
    canonical seeds (the Pell convergents' boundary fractions
    0/1 and 1/0)
  · `mobiusEq cx cy` — agreement on both P-orbits, ∀ n
  · refl / symm / trans (mobiusEq is an equivalence relation)
  · `mobiusEq_of_cutEq` — pointwise equality implies P-orbit
    equality (unconditional forward direction)

## Relation to full Stern-Brocot coverage

Pure P-iteration is `R · L` in the standard SL₂(ℤ) generators
(L = [[1,0],[1,1]], R = [[1,1],[0,1]]); it walks one diagonal
of the Stern-Brocot tree per seed.  The two P-orbits therefore
cover only the Pell-convergent chains, NOT every coprime pair.
Full Stern-Brocot coverage uses the *mediant* closure
(a, b) ⊕ (c, d) = (a+c, b+d), giving a strictly stronger
equivalence `sternBrocotEq` (see `Mobius213SternBrocot.lean`)
with `mobiusEq` weaker than `sternBrocotEq` weaker than `cutEq`.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Real213.Mobius213Equiv

open E213.Lib.Math.Real213.Core.CutPoset (cutEq)

/-! ## §1 — P-iteration on Nat × Nat -/

/-- **P-step**: P = [[2,1],[1,1]] acts on (m, k) ↦ (2m+k, m+k).
    Identical to the iteration generating `P_numerator` /
    `P_denominator` in `Lib/Math/Mobius213.lean`. -/
def Pstep : Nat × Nat → Nat × Nat
  | (m, k) => (2 * m + k, m + k)

/-- **P-iteration**: n applications of `Pstep` starting from seed. -/
def Pseq (seed : Nat × Nat) : Nat → Nat × Nat
  | 0     => seed
  | n + 1 => Pstep (Pseq seed n)

/-- The "zero" Stern-Brocot seed: (0, 1) reads as the rational 0/1. -/
def seedZero : Nat × Nat := (0, 1)

/-- The "infinity" Stern-Brocot seed: (1, 0) reads as the
    rational 1/0 (the point at infinity on the Stern-Brocot tree). -/
def seedInf : Nat × Nat := (1, 0)

/-! ## §2 — Concrete orbit values (decidable smoke witnesses) -/

/-- Pseq from seedZero, layers 0–5: (0,1), (1,1), (3,2), (8,5),
    (21,13), (55,34).  The pairs are the Fibonacci-indexed Pell
    convergents (one-step shifted from `Lib/Math/Mobius213.lean`
    `P_numerator` / `P_denominator`). -/
theorem Pseq_seedZero_values :
    Pseq seedZero 0 = (0, 1)
    ∧ Pseq seedZero 1 = (1, 1)
    ∧ Pseq seedZero 2 = (3, 2)
    ∧ Pseq seedZero 3 = (8, 5)
    ∧ Pseq seedZero 4 = (21, 13)
    ∧ Pseq seedZero 5 = (55, 34) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Pseq from seedInf, layers 0–5: (1,0), (2,1), (5,3), (13,8),
    (34,21), (89,55).  Directly the `P_numerator` /
    `P_denominator` sequences from `Lib/Math/Mobius213.lean`. -/
theorem Pseq_seedInf_values :
    Pseq seedInf 0 = (1, 0)
    ∧ Pseq seedInf 1 = (2, 1)
    ∧ Pseq seedInf 2 = (5, 3)
    ∧ Pseq seedInf 3 = (13, 8)
    ∧ Pseq seedInf 4 = (34, 21)
    ∧ Pseq seedInf 5 = (89, 55) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The two orbits at depth 2 hit `(3, 2)` and `(5, 3)`: the Raw
    atomicity (NS, NT) = (3, 2) appears in the first orbit at
    depth 2, and (NS + NT, NS) = (5, 3) appears in the second. -/
theorem orbits_hit_atoms_at_depth_2 :
    Pseq seedZero 2 = (3, 2) ∧ Pseq seedInf 2 = (5, 3) :=
  ⟨rfl, rfl⟩

/-! ## §3 — mobiusEq: agreement on both P-orbits -/

/-- **mobiusEq**: two cuts agree on the (0,1)- and (1,0)-orbits
    under P-iteration.  This is a *weak* equality: the two
    P-orbits only sample the Pell-convergent chains, not the
    full Stern-Brocot tree.  Strictly weaker than `cutEq`;
    strictly weaker than `sternBrocotEq` (the mediant-closure
    version in `Mobius213SternBrocot.lean`).  Forward bridge
    `cutEq → mobiusEq` is unconditional (`mobiusEq_of_cutEq`). -/
def mobiusEq (cx cy : Nat → Nat → Bool) : Prop :=
  ∀ n,
    cx (Pseq seedZero n).1 (Pseq seedZero n).2
      = cy (Pseq seedZero n).1 (Pseq seedZero n).2
    ∧ cx (Pseq seedInf  n).1 (Pseq seedInf  n).2
      = cy (Pseq seedInf  n).1 (Pseq seedInf  n).2

/-! ## §4 — mobiusEq is an equivalence relation -/

/-- mobiusEq reflexivity. -/
theorem mobiusEq_refl (c : Nat → Nat → Bool) : mobiusEq c c :=
  fun _ => ⟨rfl, rfl⟩

/-- mobiusEq symmetry. -/
theorem mobiusEq_symm (cx cy : Nat → Nat → Bool) :
    mobiusEq cx cy → mobiusEq cy cx := by
  intro h n
  have hn := h n
  exact ⟨hn.1.symm, hn.2.symm⟩

/-- mobiusEq transitivity. -/
theorem mobiusEq_trans (cx cy cz : Nat → Nat → Bool) :
    mobiusEq cx cy → mobiusEq cy cz → mobiusEq cx cz := by
  intro h1 h2 n
  have h1n := h1 n
  have h2n := h2 n
  exact ⟨h1n.1.trans h2n.1, h1n.2.trans h2n.2⟩

/-! ## §5 — Forward bridge: cutEq ⇒ mobiusEq -/

/-- ★★★ **Forward direction**: pointwise equality on all
    `(m, k)` implies agreement on the two Stern-Brocot orbits.
    Trivial pointwise specialisation; recorded as the half of
    the conjecture that holds unconditionally. -/
theorem mobiusEq_of_cutEq (cx cy : Nat → Nat → Bool) :
    cutEq cx cy → mobiusEq cx cy := by
  intro h n
  exact ⟨h (Pseq seedZero n).1 (Pseq seedZero n).2,
         h (Pseq seedInf  n).1 (Pseq seedInf  n).2⟩

end E213.Lib.Math.Real213.Mobius213Equiv
