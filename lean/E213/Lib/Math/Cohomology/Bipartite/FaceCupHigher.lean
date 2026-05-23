import E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology
import E213.Lib.Math.Cohomology.Bipartite.SelfPairingTrace
import E213.Lib.Math.Cohomology.Cup.SteenrodHigherFrame

/-!
# Higher cup operations on Filled3Cell face cochains

Extends the Steenrod cup-i framework from `Cup/SteenrodHigherFrame.lean`
to the `K_{3,2}^{(c=2)}` face-cochain setting (face cochains
`Fin 3 → Bool` modelling the 3 simple 4-cycles at full filling).

## Why face cup-i for the (k+1) frontier

The H² ω class lives in `C² = Fin 3 → Bool` directly (not as
`Cochain 5 k` on Δ⁴).  Self-pairing ω at the face level requires
a cup-i operation tailored to this bipartite multigraph cochain
structure.

`face_cup_0` (bilinear pointwise) and `face_cup_2` (also bilinear
pointwise but conceptually at the "diagonal" of the cup-i family)
both land in `Fin 3 → Bool` — the simplest closed cup-i instances
on face cochains.

## Cup ladder graduation (k=2 → α³ via face-cup iteration)

For ω at H² (cohomology degree 2), the cup-i ladder

      ω ⌣_0 ω : Fin 3 → Bool ⊗ Fin 3 → Bool (degree 4, off-complex)
      ω ⌣_1 ω : Fin 3 → Bool (degree 3, would need 3-cell extension)
      ω ⌣_2 ω : Fin 3 → Bool (degree 2, back to face cochain) ★

shows that `cup_2` is the natural self-pairing operation at H²
that lands in the existing complex.  This is the **degree-2 cup-i
analog of the standard bilinear cup at H¹**.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.FaceCupHigher

open E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology
open E213.Lib.Math.Cohomology.Bipartite.SelfPairingTrace

/-! ## §1 — face_cup_2: bilinear self-pairing on face cochains -/

/-- Face-cup-2 on `K_{3,2}^{(c=2)}` 2-cochains:

      face_cup_2 (α, β) (face_i) := α(face_i) ∧ β(face_i).

    Pointwise Bool conjunction.  This is the simplest cup-i
    instance at face level that lands back in `Fin 3 → Bool`. -/
def face_cup_2 (α β : Fin 3 → Bool) : Fin 3 → Bool :=
  fun i => α i && β i

/-! ## §2 — face_cup_2 properties -/

/-- ★★★ face_cup_2 is symmetric. -/
theorem face_cup_2_symmetric (α β : Fin 3 → Bool) (i : Fin 3) :
    face_cup_2 α β i = face_cup_2 β α i := by
  unfold face_cup_2
  cases α i <;> cases β i <;> rfl

/-- ★★★ face_cup_2 is zero-preserving. -/
theorem face_cup_2_zero_left (β : Fin 3 → Bool) (i : Fin 3) :
    face_cup_2 (fun _ => false) β i = false := by
  unfold face_cup_2
  rfl

/-! ## §3 — face_cup_2 on the ω class

The H² ω class is `omega_face_vec = fun _ => true`.  Its
self-cup_2 is again all-true (pointwise true ∧ true). -/

/-- ★★★★ Self-cup_2 of ω: `ω ⌣_2 ω = ω`.

    Algebraically: `(1, 1, 1) ⌣_2 (1, 1, 1) = (1∧1, 1∧1, 1∧1) =
    (1, 1, 1)`.  ω is idempotent under face_cup_2. -/
theorem omega_cup_2_self : ∀ i, face_cup_2 omega_face_vec omega_face_vec i = true := by
  intro i
  unfold face_cup_2 omega_face_vec
  rfl

/-- ★★★★ Self-cup_2 of ω equals ω (function equality form). -/
theorem omega_cup_2_self_eq_omega :
    ∀ i, face_cup_2 omega_face_vec omega_face_vec i = omega_face_vec i := by
  intro i
  unfold face_cup_2 omega_face_vec
  rfl

/-! ## §4 — Bilinear self-trace via face_cup_2

The trace of `ω ⌣_2 ω` at top equals the bilinear self-pairing
trace of ω (since `ω ⌣_2 ω = ω`).  This is the cup-i route to the
same L²-pairing trace that `SelfPairingTrace.bilinearSelfTrace`
computes via the explicit face-pair sum. -/

/-- ★★★★ Self-cup_2 trace of ω equals `bilinearSelfTrace ω = 9 = NS²`. -/
theorem omega_cup_2_self_trace_eq_NS_sq :
    bilinearSelfTrace (face_cup_2 omega_face_vec omega_face_vec) = 9 := by
  -- face_cup_2 ω ω = ω pointwise, so bilinearSelfTrace of either is the same
  -- direct decide
  decide

/-- ★★★★★ Self-cup_2 trace agreement: `bilinearSelfTrace (ω ⌣_2 ω) = NS² = bilinearSelfTrace ω`.
    Demonstrates that the cup-i route lands at the same L²-pairing
    weight as the direct bilinear self-pairing. -/
theorem omega_cup_2_trace_matches_direct :
    bilinearSelfTrace (face_cup_2 omega_face_vec omega_face_vec)
      = bilinearSelfTrace omega_face_vec := by
  decide

/-! ## §5 — Phase 9.2 master -/

/-- ★★★★★★★★ **FaceCupHigher master**.  STRICT ∅-AXIOM.

    Extends the Steenrod cup-i framework to `K_{3,2}^{(c=2)}` face
    cochains via the explicit `face_cup_2 : (Fin 3 → Bool)² → (Fin 3 → Bool)`
    operation (pointwise Bool conjunction).

    Key results:
      · `face_cup_2_symmetric`: face_cup_2 α β = face_cup_2 β α
      · `face_cup_2_zero_left`: zero-preserving in the left argument
      · `omega_cup_2_self`: ω ⌣_2 ω = (true, true, true)
      · `omega_cup_2_self_eq_omega`: ω ⌣_2 ω = ω (ω is idempotent)
      · `omega_cup_2_self_trace_eq_NS_sq`: trace(ω ⌣_2 ω) = NS² = 9
      · `omega_cup_2_trace_matches_direct`: cup-i route gives the
        same L²-pairing trace as direct bilinear

    Status of the cup-i → (k+1) graduation derivation:

      | Component | Status |
      |-----------|--------|
      | cup-i type framework | DEFINED (`SteenrodHigherFrame`) |
      | cup_0 = standard cup at (5, 1, 1) | PROVED |
      | cup_1 at (5, 1, 1), (5, 1, 2) | DEFINED |
      | face_cup_2 on Filled3Cell face cochains | DEFINED (this file) |
      | ω self-cup_2 idempotent | PROVED |
      | ω self-cup_2 trace = NS² (matches Phase 6) | PROVED |
      | General cup_i for arbitrary i ≥ 2 | OPEN (full Alexander-Whitney) |
      | (k+1) graduation derivation from cup_i ladder | OPEN (needs 3-cell extension) |

    The face_cup_2 idempotency `ω ⌣_2 ω = ω` shows that at the
    face-cochain level the cup-i self-pairing collapses to ω
    itself.  The structural content is in the TRACE evaluation,
    not in the cup-product output.  This separates two structural
    factors:
      · Cup-i output (here: ω idempotent under face_cup_2);
      · Trace evaluation weight (here: NS² from L¹-norm-squared).

    Full derivation of `(k+1)` α-power graduation from cup-i
    ladder remains open pending:
      (a) 3-cell extension of `K_{3,2}^{(c=2)}` (so cup_1(ω, ω) at
          degree 3 lands at top of a 3-skeleton);
      (b) Steenrod algebra Adem/Cartan relations to give the
          graduation pattern axiomatically. -/
theorem face_cup_higher_master :
    -- face_cup_2 basic properties
    (∀ α β : Fin 3 → Bool, ∀ i, face_cup_2 α β i = face_cup_2 β α i)
    ∧ (∀ β : Fin 3 → Bool, ∀ i, face_cup_2 (fun _ => false) β i = false)
    -- ω self-pairing under face_cup_2
    ∧ (∀ i, face_cup_2 omega_face_vec omega_face_vec i = true)
    ∧ (∀ i, face_cup_2 omega_face_vec omega_face_vec i = omega_face_vec i)
    -- Trace matches L²-pairing weight
    ∧ bilinearSelfTrace (face_cup_2 omega_face_vec omega_face_vec) = 9
    ∧ bilinearSelfTrace (face_cup_2 omega_face_vec omega_face_vec)
        = bilinearSelfTrace omega_face_vec := by
  refine ⟨face_cup_2_symmetric, face_cup_2_zero_left,
          omega_cup_2_self, omega_cup_2_self_eq_omega,
          omega_cup_2_self_trace_eq_NS_sq,
          omega_cup_2_trace_matches_direct⟩

end E213.Lib.Math.Cohomology.Bipartite.FaceCupHigher
