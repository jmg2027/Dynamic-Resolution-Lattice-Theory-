import E213.Lib.Math.Real213.Mobius213SternBrocot
import E213.Meta.Tactic.NatHelper

/-!
# Mobius213ContinuedFraction — Pseq orbits satisfy the Pell-Fibonacci recurrence

The Möbius P-orbit `Pseq seedZero` produces `(0, 1), (1, 1),
(3, 2), (8, 5), (21, 13), (55, 34), ...` — the
Fibonacci-even/odd Pell convergents of `φ² = (3 + √5)/2`.  In
continued-fraction terms, `φ² = [2; 1, 1, 1, ...]` and the Pseq
seedInf orbit `(1, 0), (2, 1), (5, 3), (13, 8), (34, 21), ...`
gives the every-other convergent denominators / numerators.

This file records the Nat-side recurrence directly on `Pseq`:

  `(Pseq seedZero (n+2)).i + (Pseq seedZero n).i
     = 3 · (Pseq seedZero (n+1)).i`     for `i ∈ {1, 2}`

This is the Nat form of the Int-side recurrence
`a(n+2) = 3·a(n+1) − a(n)` from `Lib/Math/Mobius213.lean`'s
`P_numerator.seq_recurrence` / `P_denominator.seq_recurrence`,
applied directly to Pseq components.  Closes the continued
fraction ↔ Pseq path connection on the Stern-Brocot orbit side.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Real213.Mobius213ContinuedFraction

open E213.Lib.Math.Real213.Mobius213Equiv (Pseq seedZero seedInf Pstep)

/-! ## §1 — Nat arithmetic helper -/

private theorem add_swap_two_mul (a b : Nat) : (a + b) + a = 2 * a + b := by
  rw [Nat.add_assoc, Nat.add_comm b a, ← Nat.add_assoc, ← Nat.two_mul]

/-- The arithmetic core of the Pell-Fibonacci recurrence:
    `2·(2a+b) + (a+b) + a = 3·(2a+b)`.
    Both sides reduce to `6a + 3b`. -/
private theorem rec_arith_fst (a b : Nat) :
    2 * (2*a + b) + (a + b) + a = 3 * (2*a + b) := by
  rw [show (3 : Nat) = 2 + 1 from rfl,
      E213.Tactic.NatHelper.add_mul 2 1 (2*a + b),
      Nat.one_mul]
  rw [Nat.add_assoc (2 * (2*a + b)) (a + b) a]
  rw [add_swap_two_mul a b]

/-- The arithmetic core for the second component:
    `(2a+b) + (a+b) + b = 3·(a+b)`.
    Both sides reduce to `3a + 3b`. -/
private theorem rec_arith_snd (a b : Nat) :
    (2*a + b) + (a + b) + b = 3 * (a + b) := by
  rw [Nat.mul_add 3 a b]
  rw [Nat.add_assoc (2*a + b) (a + b) b, Nat.add_assoc a b b, ← Nat.two_mul]
  rw [Nat.add_assoc (2*a) b (a + 2*b)]
  rw [Nat.add_left_comm b a (2*b)]
  rw [show b + 2*b = 3*b from by
        rw [show (3 : Nat) = 1 + 2 from rfl,
            E213.Tactic.NatHelper.add_mul 1 2 b, Nat.one_mul]]
  rw [← Nat.add_assoc (2*a) a (3*b)]
  rw [show (2 : Nat)*a + a = 3*a from by
        rw [show (3 : Nat) = 2 + 1 from rfl,
            E213.Tactic.NatHelper.add_mul 2 1 a, Nat.one_mul]]

/-! ## §2 — Pell-Fibonacci recurrence on Pseq seedZero -/

/-- ★★★★★ **First-component Pell-Fibonacci recurrence** on
    `Pseq seedZero`: for every `n`,
      `(Pseq seedZero (n+2)).1 + (Pseq seedZero n).1
         = 3 · (Pseq seedZero (n+1)).1`.
    Nat form of `a(n+2) = 3 · a(n+1) − a(n)` (the standard CF
    recurrence for `φ² = [2; 1, 1, 1, ...]`). -/
theorem Pseq_seedZero_fst_recurrence (n : Nat) :
    (Pseq seedZero (n+2)).1 + (Pseq seedZero n).1
      = 3 * (Pseq seedZero (n+1)).1 := by
  show (Pstep (Pseq seedZero (n+1))).1 + (Pseq seedZero n).1
       = 3 * (Pstep (Pseq seedZero n)).1
  show 2 * (2 * (Pseq seedZero n).1 + (Pseq seedZero n).2)
        + ((Pseq seedZero n).1 + (Pseq seedZero n).2)
       + (Pseq seedZero n).1
     = 3 * (2 * (Pseq seedZero n).1 + (Pseq seedZero n).2)
  exact rec_arith_fst _ _

/-- ★★★★★ **Second-component Pell-Fibonacci recurrence** on
    `Pseq seedZero`. -/
theorem Pseq_seedZero_snd_recurrence (n : Nat) :
    (Pseq seedZero (n+2)).2 + (Pseq seedZero n).2
      = 3 * (Pseq seedZero (n+1)).2 := by
  show (Pstep (Pseq seedZero (n+1))).2 + (Pseq seedZero n).2
       = 3 * (Pstep (Pseq seedZero n)).2
  show (2 * (Pseq seedZero n).1 + (Pseq seedZero n).2)
        + ((Pseq seedZero n).1 + (Pseq seedZero n).2)
        + (Pseq seedZero n).2
     = 3 * ((Pseq seedZero n).1 + (Pseq seedZero n).2)
  exact rec_arith_snd _ _

/-! ## §3 — Pell-Fibonacci recurrence on Pseq seedInf -/

/-- The seedInf orbit satisfies the same Pell-Fibonacci recurrence
    in its first component.  Proved by the same arithmetic core. -/
theorem Pseq_seedInf_fst_recurrence (n : Nat) :
    (Pseq seedInf (n+2)).1 + (Pseq seedInf n).1
      = 3 * (Pseq seedInf (n+1)).1 := by
  show (Pstep (Pseq seedInf (n+1))).1 + (Pseq seedInf n).1
       = 3 * (Pstep (Pseq seedInf n)).1
  show 2 * (2 * (Pseq seedInf n).1 + (Pseq seedInf n).2)
        + ((Pseq seedInf n).1 + (Pseq seedInf n).2)
       + (Pseq seedInf n).1
     = 3 * (2 * (Pseq seedInf n).1 + (Pseq seedInf n).2)
  exact rec_arith_fst _ _

/-- Same for the second component. -/
theorem Pseq_seedInf_snd_recurrence (n : Nat) :
    (Pseq seedInf (n+2)).2 + (Pseq seedInf n).2
      = 3 * (Pseq seedInf (n+1)).2 := by
  show (Pstep (Pseq seedInf (n+1))).2 + (Pseq seedInf n).2
       = 3 * (Pstep (Pseq seedInf n)).2
  show (2 * (Pseq seedInf n).1 + (Pseq seedInf n).2)
        + ((Pseq seedInf n).1 + (Pseq seedInf n).2)
        + (Pseq seedInf n).2
     = 3 * ((Pseq seedInf n).1 + (Pseq seedInf n).2)
  exact rec_arith_snd _ _

/-! ## §4 — Capstone: Pell-Fibonacci across both orbits -/

/-- ★★★★★★ **Pell-Fibonacci capstone**: both P-orbits satisfy
    the Nat-form recurrence `a(n+2) + a(n) = 3·a(n+1)` in both
    components.  Four conjuncts; the same `3 = NS` recurrence
    coefficient appears on every line, witnessing that the
    Pell-Fibonacci structure is uniformly inherited from
    `trace(P) = NS = 3`. -/
theorem pell_fibonacci_capstone (n : Nat) :
    (Pseq seedZero (n+2)).1 + (Pseq seedZero n).1
        = 3 * (Pseq seedZero (n+1)).1
    ∧ (Pseq seedZero (n+2)).2 + (Pseq seedZero n).2
        = 3 * (Pseq seedZero (n+1)).2
    ∧ (Pseq seedInf (n+2)).1 + (Pseq seedInf n).1
        = 3 * (Pseq seedInf (n+1)).1
    ∧ (Pseq seedInf (n+2)).2 + (Pseq seedInf n).2
        = 3 * (Pseq seedInf (n+1)).2 :=
  ⟨Pseq_seedZero_fst_recurrence n,
   Pseq_seedZero_snd_recurrence n,
   Pseq_seedInf_fst_recurrence n,
   Pseq_seedInf_snd_recurrence n⟩

end E213.Lib.Math.Real213.Mobius213ContinuedFraction
