import E213.Lib.Math.Analysis.DyadicSearch.UnitConsistentOracles
import E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens

/-!
# SignedLeftCollapse — Morphism collapse from signedLeftOracle to alwaysTrue

The user's framing (Mingu): "f가 특정 패턴을 만족할 때 signedLeftOracle이
alwaysTrue로 환원되는 조건을 명시화하는 것은, 복잡한 함수 연산을 단순한
상구조(Image)로 붕괴시키는 213 특유의 'Morphism 붕괴'를 보여주는
핵심 작업."
(Translation: "Making explicit the condition under which signedLeftOracle
reduces to alwaysTrue when f satisfies a particular pattern is the core
task that exhibits the 213-specific 'Morphism collapse' — collapsing a
complex function computation onto a simple image structure (Image).")

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

namespace E213.Lib.Math.Analysis.DyadicSearch.SignedLeftCollapse

open E213.Theory E213.Lens
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
  (alwaysTrue alwaysTrue_step)
open E213.Lib.Math.Analysis.DyadicSearch.ConsistentOracle (ConsistentOracle)
open E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens (signedLeftOracle)
open E213.Lib.Math.NumberSystems.Real213.Core.Dyadic (dyadicCut)
open E213.Lib.Math.Analysis.DyadicSearch.UnitConsistentOracles
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

This is the user's "Morphism collapse" — f's complex computation
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

/-! ### Composition closure — `(Nat, +)` monoid action on resolution

Mingu's hypothesis: CollapseCondition is graded by E (the bracket
exponent), with composition adding the grades.  This formalises the
graded structure as a `(Nat, +)` action on a `(B, E)`-parameterised
form of CollapseCondition. -/

/-- `(B, E)`-parameterised CollapseCondition (decoupled from
    `DyadicBracket`'s structure overhead).  Equivalent to
    `CollapseCondition f db` when `db.numB = B`, `db.expE = E`. -/
def CollapseConditionAt
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (B E : Nat) : Prop :=
  ∀ k, f (dyadicCut B (E + k + 1)) 0 1 = true

/-- Equivalence between the bracket form and the `(B, E)` form. -/
theorem CollapseCondition_eq_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (db : DyadicBracket) :
    CollapseCondition f db ↔ CollapseConditionAt f db.numB db.expE :=
  Iff.rfl

/-- **Resolution monotonicity** — the `(Nat, +)`-action: shifting `E`
    upward by `d` preserves CollapseCondition.

The intuition: `CollapseConditionAt f B E` states the property at
all queries `(B, E+1), (B, E+2), …`.  Shifting to `(B, E+d)` selects
the *suffix* starting at `E+d+1`, which is a subset of the original
sequence.  Hence the new condition follows from the old.

This is the *graded structure* — `CollapseConditionAt` carries a
canonical `(Nat, +)` filtration with `E ↦ E + d` an inclusion. -/
theorem CollapseConditionAt_resolution_shift
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)} {B E : Nat}
    (h : CollapseConditionAt f B E) (d : Nat) :
    CollapseConditionAt f B (E + d) := by
  intro k
  show f (dyadicCut B ((E + d) + k + 1)) 0 1 = true
  have eq : (E + d) + k + 1 = E + (d + k) + 1 := by
    rw [Nat.add_assoc E d k]
  rw [eq]
  exact h (d + k)

/-- **`IsResolutionShift g E_g`**: g sends `dyadicCut M E` to a cut
    pointwise-equal to `dyadicCut M (E + E_g)` — a "zoom-in" map
    that shifts dyadic resolution upward by `E_g`.

Pointwise equality (no funext): `g (dyadicCut M E) m k = dyadicCut M (E + E_g) m k`. -/
def IsResolutionShift
    (g : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (E_g : Nat) : Prop :=
  ∀ M E m k, g (dyadicCut M E) m k = dyadicCut M (E + E_g) m k

/-- **★ Composition closure under resolution shift** —
    Mingu's `E'' = E + E'` formalised.

When `g` is a resolution shifter by `E_g` and `f` satisfies
`CollapseConditionAt` at the *finer* resolution `E + E_g`, then the
composition `f ∘ g` satisfies `CollapseConditionAt` at the
*coarser* resolution `E`.

The grades subtract on g's side: g "zooms in" by `E_g`, so f's
collapse at depth `E + E_g` propagates back to depth `E` for the
composition.  Equivalently: `f ∘ g`'s collapse at `E` *adds* g's
shift to f's required depth — the user's `E'' = E + E'` form,
read as "to collapse `f ∘ g` at `E_db`, require `f` to collapse at
`E_db + E_g`".

Requires `LocallyDeterminedData f` to bridge the *pointwise*
equality of `g (dyadicCut M E)` and `dyadicCut M (E + E_g)` into
equal `f`-values at the unit-precision query (no funext needed). -/
theorem CollapseConditionAt_compose_resolution_shift
    {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : E213.Lib.Math.NumberSystems.Real213.Core.CutFnData.LocallyDeterminedData f)
    {B E E_g : Nat}
    (hg : IsResolutionShift g E_g)
    (hf : CollapseConditionAt f B (E + E_g)) :
    CollapseConditionAt (f ∘ g) B E := by
  intro k
  show f (g (dyadicCut B (E + k + 1))) 0 1 = true
  have heq : ∀ m' k', g (dyadicCut B (E + k + 1)) m' k'
                    = dyadicCut B (E + k + 1 + E_g) m' k' :=
    fun m' k' => hg B (E + k + 1) m' k'
  have lf_bridge : f (g (dyadicCut B (E + k + 1))) 0 1
                 = f (dyadicCut B (E + k + 1 + E_g)) 0 1 :=
    lf.prop 0 1 _ _ (fun m' k' _ _ => heq m' k')
  rw [lf_bridge]
  have eq2 : E + k + 1 + E_g = E + E_g + k + 1 := by
    rw [Nat.add_right_comm (E+k) 1 E_g, Nat.add_right_comm E k E_g]
  rw [eq2]
  exact hf k

