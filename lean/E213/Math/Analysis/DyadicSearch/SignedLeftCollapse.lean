import E213.Math.Analysis.DyadicSearch.UnitConsistentOracles
import E213.Math.Analysis.DyadicSearch.MinimalRootLens

/-!
# SignedLeftCollapse — Morphism collapse from signedLeftOracle to alwaysTrue

The user's framing (Mingu): "f가 특정 패턴을 만족할 때 signedLeftOracle이
alwaysTrue로 환원되는 조건을 명시화하는 것은, 복잡한 함수 연산을 단순한
상구조(Image)로 붕괴시키는 213 특유의 'Morphism 붕괴'를 보여주는
핵심 작업."

## What's closed here

When `f` satisfies the **collapse condition** at a starting bracket
`db` with `numA = 0`:

  ∀ k, f (dyadicCut db.numB (db.expE + k + 1)) 0 1 = true

— i.e., f is "true at unit precision on the alwaysTrue-bracket
midCut sequence" — then the entire trajectory under
`signedLeftOracle f` is *structurally identical* to the trajectory
under `alwaysTrue`.

This collapses the f-driven oracle into the constant oracle: the
ConsistentOracle for `signedLeftOracle f` from `db` is *exactly*
the ConsistentOracle for `alwaysTrue` (already constructed in
`UnitConsistentOracles`).

## Architectural significance

  * **Reductionist proof**: complex f-computation collapses to a
    constant Bool image when f's unit-precision pattern aligns
    with the bracket's natural trajectory.
  * **Automated IVT**: once the collapse condition holds,
    `cutEq (f c) 0` follows from the alwaysTrue trajectory's
    closed-form analysis — no further f-specific work.
-/

namespace E213.Math.Analysis.DyadicSearch.SignedLeftCollapse

open E213.Firmware E213.Hypervisor
open E213.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory
  (alwaysTrue alwaysTrue_step)
open E213.Math.Analysis.DyadicSearch.ConsistentOracle (ConsistentOracle)
open E213.Math.Analysis.DyadicSearch.MinimalRootLens (signedLeftOracle)
open E213.Math.Real213.Dyadic (dyadicCut)
open E213.Math.Analysis.DyadicSearch.UnitConsistentOracles
  (numA_zero_alwaysTrue_ConsistentOracle)

/-- **Collapse condition**: at the alwaysTrue trajectory's midCut
    sequence (closed form `dyadicCut db.numB (db.expE + k + 1)`),
    f is `true` at unit precision for every depth `k`.

This is the structural pattern that "simplifies" `signedLeftOracle f`
to `alwaysTrue` from a `numA = 0` bracket. -/
def CollapseCondition
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) : Prop :=
  ∀ k, f (dyadicCut db.numB (db.expE + k + 1)) 0 1 = true

/-- **Trajectory equivalence under collapse**: when the collapse
    condition holds and `db.numA = 0`, the trajectory under
    `signedLeftOracle f` from `db` equals the trajectory under
    `alwaysTrue` at every depth.

Proof: induction on `n`.  Each step uses the collapse hypothesis
at `k = 0` to show `f db.midCut 0 1 = true`, hence
`signedLeftOracle f db.midCut = true = alwaysTrue db.midCut`, so
the bisection step is identical.  The inductive hypothesis is
strengthened over all `db'` satisfying the same shape; collapse is
propagated to `db.leftHalf` via index shift. -/
theorem signedLeftOracle_eq_alwaysTrue_traj
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) :
    ∀ n db, db.numA = 0 → CollapseCondition f db →
      DyadicBracket.bisectN (signedLeftOracle f) n db
      = DyadicBracket.bisectN alwaysTrue n db
  | 0, _, _, _ => rfl
  | n+1, db, h, collapse => by
    show DyadicBracket.bisectN (signedLeftOracle f) n
            (db.bisectStep (signedLeftOracle f))
       = DyadicBracket.bisectN alwaysTrue n
            (db.bisectStep alwaysTrue)
    have hf : f db.midCut 0 1 = true := by
      show f (dyadicCut (db.numA + db.numB) (db.expE + 1)) 0 1 = true
      rw [h, Nat.zero_add]
      exact collapse 0
    have hstep : db.bisectStep (signedLeftOracle f) = db.bisectStep alwaysTrue := by
      show (bif signedLeftOracle f db.midCut then db.leftHalf else db.rightHalf)
         = (bif alwaysTrue db.midCut then db.leftHalf else db.rightHalf)
      rw [show signedLeftOracle f db.midCut = true from hf]
      rfl
    rw [hstep]
    have h' : db.leftHalf.numA = 0 := by
      show 2 * db.numA = 0
      rw [h, Nat.mul_zero]
    have collapse' : CollapseCondition f db.leftHalf := by
      intro k
      show f (dyadicCut (db.numA + db.numB) (db.expE + 1 + k + 1)) 0 1 = true
      rw [h, Nat.zero_add]
      have eq : db.expE + 1 + k + 1 = db.expE + (k + 1) + 1 := by
        rw [Nat.add_assoc db.expE 1 k, Nat.add_comm 1 k]
      rw [eq]
      exact collapse (k + 1)
    rw [alwaysTrue_step db]
    exact signedLeftOracle_eq_alwaysTrue_traj f n db.leftHalf h' collapse'

/-- midCut equality at every depth (corollary of trajectory
    equivalence). -/
theorem signedLeftOracle_midCut_eq_alwaysTrue
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) (h : db.numA = 0) (collapse : CollapseCondition f db)
    (n : Nat) :
    (DyadicBracket.bisectN (signedLeftOracle f) n db).midCut
    = (DyadicBracket.bisectN alwaysTrue n db).midCut := by
  rw [signedLeftOracle_eq_alwaysTrue_traj f n db h collapse]

/-- **★ Morphism collapse — the closure**: under the collapse
    condition + `numA = 0`, the `signedLeftOracle f`-driven
    ConsistentOracle on `db` is *constructible* by structurally
    reducing to `numA_zero_alwaysTrue_ConsistentOracle db`.

This is the user's "Morphism 붕괴" — f's complex computation
collapses to a constant-Bool image once its unit-precision pattern
aligns with the bracket's natural alwaysTrue trajectory. -/
def signedLeft_collapseTo_alwaysTrue_ConsistentOracle
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) (h : db.numA = 0) (collapse : CollapseCondition f db) :
    ConsistentOracle db where
  oracle := signedLeftOracle f
  thresholdN := fun _ k => db.numB * k
  consistency := by
    intro m k n1 n2 hn1 hn2
    rw [signedLeftOracle_midCut_eq_alwaysTrue f db h collapse n1,
        signedLeftOracle_midCut_eq_alwaysTrue f db h collapse n2]
    exact (numA_zero_alwaysTrue_ConsistentOracle db h).consistency
            m k n1 n2 hn1 hn2

end E213.Math.Analysis.DyadicSearch.SignedLeftCollapse

