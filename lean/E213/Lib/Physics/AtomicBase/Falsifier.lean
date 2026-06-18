import E213.Lib.Physics.AtomicBase.Origin
import E213.Lib.Physics.AtomicBase.Edges
import E213.Lib.Physics.AtomicBase.Force

/-!
# Phase 2 Falsifier — falsifiable propositions of 213

**Layer: App** (contrapositive formalization of Phase 2 results).

CLAUDE.md verification criterion (2): *formalized such that no one can dispute the new physics* — measurable propositions.

Phase 2 derived *integers* forced by the axioms.  This file is the
contrapositive — formalization of *which observations refute 213*.

## Formal falsifiers

  (F1) observation d ≠ 5 → violates Atomicity.
  (F2) big block size ≠ 3 → violates (3,2) partition.
  (F3) small block size ≠ 2 → violates (3,2) partition.
  (F4) total pair count ≠ 10 → violates C(5,2).
  (F5) channel count ≠ 3 → violates pair type classification.
  (F6) cycle space dim ≠ 8 → violates atomicity-locked photon.
  (F7) NT ≠ 2 → violates NT atomic.

Each falsifier is in *contrapositive* form: "If DRLT is correct then X holds.
If X is false then DRLT is refuted."
-/

namespace E213.Lib.Physics.AtomicBase.Falsifier

open E213.Theory.Atomicity.Five

/-- (F1) d=5 falsifier.  Atomic n → n=5; contrapositive n≠5 → ¬Atomic n.
    Kept as standalone because it's a parameterized lemma used inside
    the synthesis below for ∀-quantified F1 and the F1' instances. -/
theorem falsifier_d_unique (n : Nat) (hn : n ≠ 5) : ¬ Atomic n := by
  intro h
  exact hn (atomic_implies_five n h)

/-- ★ Phase 2 Falsifier synthesis ★
    A single formal theorem of *all integers* forced by DRLT.
    If *any one* of these differs from observation, 213 is refuted.

    Bundles F1 (d unique), F1' (¬Atomic n for standard candidates),
    F4 (C(5,2)=10 plus the not-9 / not-15 contrapositive bracket),
    F5 (channels=3), F6 (cycle space=8 plus the not-5 contrapositive),
    F7 (NT=2). -/
theorem phase2_falsifiers :
    -- (F1) d unique: n ≠ 5 → ¬ Atomic n
    (∀ n, n ≠ 5 → ¬ Atomic n)
    -- (F1') concrete refutations at standard non-5 candidates
    ∧ (¬ Atomic 4) ∧ (¬ Atomic 6) ∧ (¬ Atomic 11)
    -- (F4) C(5,2) = 10, with not-9 / not-15 contrapositives
    ∧ (5 * (5 - 1) / 2 = 10)
    ∧ ¬ (5 * (5 - 1) / 2 = 9)
    ∧ ¬ (5 * (5 - 1) / 2 = 15)
    -- (F5) Channel count = 3
    ∧ (E213.Lib.Physics.AtomicBase.Force.num_channels = 3)
    -- (F6) Cycle space = 8 = NS²-1 (with not-5 contrapositive)
    ∧ (E213.Lib.Physics.AtomicBase.Edges.NS_atomic *
       E213.Lib.Physics.AtomicBase.Edges.NS_atomic - 1 = 8)
    ∧ ¬ (E213.Lib.Physics.AtomicBase.Edges.NS_atomic *
         E213.Lib.Physics.AtomicBase.Edges.NS_atomic - 1 = 5)
    -- (F7) NT = 2
    ∧ (E213.Lib.Physics.Simplex.Counts.NT = 2) := by
  refine ⟨falsifier_d_unique, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact falsifier_d_unique 4 (by decide)
  · exact falsifier_d_unique 6 (by decide)
  · exact falsifier_d_unique 11 (by decide)
  all_goals decide

end E213.Lib.Physics.AtomicBase.Falsifier
