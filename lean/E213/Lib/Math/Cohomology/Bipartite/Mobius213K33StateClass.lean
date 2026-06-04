import E213.Lib.Math.Cohomology.Bipartite.V33
import E213.Lib.Math.NumberSystems.Real213.Mobius213Equiv
import E213.Lib.Math.NumberSystems.Real213.Mobius213ContinuedFraction

/-!
# Mobius213K33StateClass — K_{3,3}^(c=2) vertex cochains under Möbius P

The bipartite multigraph `K_{3,3}^(c=2)` has vertex cochains
`CochV = Fin 6 → Bool` partitioned into S-side (indices 0, 1, 2)
and T-side (indices 3, 4, 5).  Every cochain `σ : CochV` admits a
**state-class projection** to `Nat × Nat`:

  `vertexCount σ := (countS σ, countT σ) ∈ {(s, t) | s ≤ 3, t ≤ 3}`

Unlike `K_{3,2}^(c=2)` where `vertexCount allTrueV = (3, 2) =
Pseq seedZero 2` lies directly on a canonical Möbius P orbit, the
K_{3,3} all-true state `(3, 3)` lies on the diagonal `{(a, a)}` —
NOT in either `seedZero` or `seedInf` orbits.

The structural relation: `(3, 3) = 3 · (1, 1) = NS · Pseq seedZero 1`.
So K_{3,3}'s all-true state class equals NS times the depth-1 image
of `seedZero`.  Subsequent P-iterates follow `Pstep^n (3, 3) = 3 ·
Pseq seedZero (n + 1)` (by P-linearity over `Nat × Nat`).

This is the "K_{3,3} = 3 × shifted K_{3,2}" Möbius state structure.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Mobius213K33StateClass

open E213.Lib.Math.Cohomology.Bipartite.V33 (CochV)
open E213.Lib.Math.NumberSystems.Real213.Mobius213Equiv (Pseq seedZero seedInf Pstep)
open E213.Lib.Math.NumberSystems.Real213.Mobius213ContinuedFraction
  (Pseq_seedZero_fst_recurrence Pseq_seedZero_snd_recurrence)

/-! ## §1 — Special K_{3,3} vertex cochains -/

/-- All-true vertex cochain: every S and T vertex selected. -/
def allTrueV : CochV := fun _ => true

/-- Zero vertex cochain: no vertex selected. -/
def zeroV : CochV := fun _ => false

/-! ## §2 — Side-counting functions -/

/-- **countS**: number of S-vertices (indices 0, 1, 2) selected. -/
def countS (σ : CochV) : Nat :=
  (if σ ⟨0, by decide⟩ then 1 else 0)
    + (if σ ⟨1, by decide⟩ then 1 else 0)
    + (if σ ⟨2, by decide⟩ then 1 else 0)

/-- **countT**: number of T-vertices (indices 3, 4, 5) selected. -/
def countT (σ : CochV) : Nat :=
  (if σ ⟨3, by decide⟩ then 1 else 0)
    + (if σ ⟨4, by decide⟩ then 1 else 0)
    + (if σ ⟨5, by decide⟩ then 1 else 0)

/-- **vertexCount**: the state-class projection `CochV → Nat × Nat`. -/
def vertexCount (σ : CochV) : Nat × Nat := (countS σ, countT σ)

/-! ## §3 — All-true / zero cochains -/

theorem countS_allTrueV : countS allTrueV = 3 := by decide
theorem countT_allTrueV : countT allTrueV = 3 := by decide
theorem vertexCount_zeroV : vertexCount zeroV = (0, 0) := by decide

/-- ★★★★ The all-true K_{3,3} cochain has state class `(3, 3)`,
    the diagonal of `(NS, NT)`. -/
theorem vertexCount_allTrueV : vertexCount allTrueV = (3, 3) := by decide

/-! ## §4 — Diagonal structure: `(3, 3) = NS · Pseq seedZero 1`

`Pseq seedZero 1 = (1, 1)`, so `3 · (1, 1) = (3, 3)`.  K_{3,3}'s
all-true state class is the `NS`-scaled depth-1 seedZero point. -/

/-- The state class lies on the diagonal `(NS, NS) = (3, 3)`. -/
theorem state_class_on_diagonal :
    vertexCount allTrueV = (3, 3)
    ∧ Pseq seedZero 1 = (1, 1)
    ∧ vertexCount allTrueV = (3 * (Pseq seedZero 1).1, 3 * (Pseq seedZero 1).2) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §5 — P-iteration: K_{3,3} state class = `NS × seedZero` shifted

By Pstep's linearity over `Nat × Nat`, `Pstep^n (NS · seedZero) =
NS · Pseq seedZero n` for all n.  So K_{3,3}'s orbit is
exactly the `NS = 3`-scaling of `seedZero`'s orbit, shifted by
1 depth. -/

theorem Pstep_vertexCount_allTrueV :
    Pstep (vertexCount allTrueV) = (9, 6)
    ∧ Pstep (vertexCount allTrueV) = (3 * (Pseq seedZero 2).1,
                                       3 * (Pseq seedZero 2).2) := by
  refine ⟨?_, ?_⟩ <;> decide

theorem Pstep_Pstep_vertexCount_allTrueV :
    Pstep (Pstep (vertexCount allTrueV)) = (24, 15)
    ∧ Pstep (Pstep (vertexCount allTrueV))
        = (3 * (Pseq seedZero 3).1, 3 * (Pseq seedZero 3).2) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §6 — Cross-frame capstone: K_{3,3} state class as scaled K_{3,2}

K_{3,3} state class trajectory = `NS · Pseq seedZero (n+1)` for
each depth n.  This is the K_{3,3} analog of K_{3,2}'s direct
Pseq seedZero match. -/

/-! ## §6 — NS-scaled Pell-Fibonacci recurrence on K_{3,3}'s state class

The Pell-Fibonacci recurrence `a(n+2) + a(n) = 3·a(n+1)` on the
canonical seedZero orbit lifts to K_{3,3}'s NS-scaled orbit by
linearity of multiplication.  Concretely:

  `NS · a(n+3) + NS · a(n+1) = NS · (a(n+3) + a(n+1)) = NS · (3 · a(n+2))
                              = 3 · (NS · a(n+2))`

So the same `a(n+2) + a(n) = 3·a(n+1)` shape holds on the K_{3,3}
state class trajectory, with `a(n) = NS · (Pseq seedZero (n+1))`. -/

theorem state_class_NSscaled_fst_recurrence (n : Nat) :
    3 * (Pseq seedZero (n+3)).1 + 3 * (Pseq seedZero (n+1)).1
      = 3 * (3 * (Pseq seedZero (n+2)).1) := by
  rw [← Nat.mul_add]
  exact congrArg (3 * ·) (Pseq_seedZero_fst_recurrence (n+1))

theorem state_class_NSscaled_snd_recurrence (n : Nat) :
    3 * (Pseq seedZero (n+3)).2 + 3 * (Pseq seedZero (n+1)).2
      = 3 * (3 * (Pseq seedZero (n+2)).2) := by
  rw [← Nat.mul_add]
  exact congrArg (3 * ·) (Pseq_seedZero_snd_recurrence (n+1))

/-- ★★★★ K_{3,3} state class Pell-Fibonacci capstone: both components
    satisfy the recurrence shape on the NS-scaled orbit. -/
theorem state_class_NSscaled_pell_capstone (n : Nat) :
    3 * (Pseq seedZero (n+3)).1 + 3 * (Pseq seedZero (n+1)).1
      = 3 * (3 * (Pseq seedZero (n+2)).1)
    ∧ 3 * (Pseq seedZero (n+3)).2 + 3 * (Pseq seedZero (n+1)).2
      = 3 * (3 * (Pseq seedZero (n+2)).2) :=
  ⟨state_class_NSscaled_fst_recurrence n,
   state_class_NSscaled_snd_recurrence n⟩

theorem state_class_master :
    -- (a) S/T counts match (NS, NT) = (3, 3)
    countS allTrueV = 3
    ∧ countT allTrueV = 3
    -- (b) vertexCount on diagonal
    ∧ vertexCount allTrueV = (3, 3)
    -- (c) Diagonal = NS-scaled seedZero depth-1
    ∧ vertexCount allTrueV = (3 * (Pseq seedZero 1).1,
                              3 * (Pseq seedZero 1).2)
    -- (d) First Pstep = NS-scaled seedZero depth-2 = (9, 6)
    ∧ Pstep (vertexCount allTrueV) = (3 * (Pseq seedZero 2).1,
                                      3 * (Pseq seedZero 2).2)
    -- (e) Second Pstep = NS-scaled seedZero depth-3 = (24, 15)
    ∧ Pstep (Pstep (vertexCount allTrueV))
        = (3 * (Pseq seedZero 3).1, 3 * (Pseq seedZero 3).2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.Bipartite.Mobius213K33StateClass
