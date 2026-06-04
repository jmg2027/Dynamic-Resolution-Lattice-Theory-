import E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumEq

/-!
# Mobius213CutSetoid — categorical packaging of the canonical equivalence

The canonical Möbius-orbit equivalence on cuts has structural
properties that make it the **setoid relation** on `Nat → Nat →
Bool` for the cut framework's algebra: it is reflexive, symmetric,
transitive, and every cut-framework operation respects it.  This
file packages those properties as a Setoid plus morphism
structures.

Quot.sound is **not** invoked anywhere: the package gives the
relation, equivalence laws, and respecting maps as bundled
structures (analogous to `LensMap` in
`Padic/SetoidFramework.lean`), but no actual quotient is taken.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mobius213CutSetoid

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
  (cutEq cutEq_refl cutEq_symm cutEq_trans)
open E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot
  (sternBrocotEq cutEq_of_sternBrocotEq sternBrocotEq_of_cutEq
   cutEq_iff_sternBrocotEq_and_zero)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
  (cutSumN cutSumN_cutEq_left cutSumN_cutEq_right)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumEq
  (cutSum_cutEq_both cutMul_cutEq_both)

/-! ## §1 — The canonical equivalence -/

/-- **Canonical cut equivalence**: Stern-Brocot mediant-orbit
    agreement plus the `(0, 0)` boundary condition.  By
    `cutEq_iff_sternBrocotEq_and_zero` this is exactly `cutEq`. -/
def CutEquiv (cx cy : Nat → Nat → Bool) : Prop :=
  sternBrocotEq cx cy ∧ cx 0 0 = cy 0 0

/-- The canonical equivalence is just `cutEq` in different
    coordinates. -/
theorem CutEquiv_iff_cutEq (cx cy : Nat → Nat → Bool) :
    CutEquiv cx cy ↔ cutEq cx cy :=
  (cutEq_iff_sternBrocotEq_and_zero cx cy).symm

/-! ## §2 — Equivalence relation laws -/

theorem CutEquiv_refl (c : Nat → Nat → Bool) : CutEquiv c c :=
  ⟨sternBrocotEq_of_cutEq c c (cutEq_refl c), rfl⟩

theorem CutEquiv_symm {cx cy : Nat → Nat → Bool}
    (h : CutEquiv cx cy) : CutEquiv cy cx :=
  ⟨fun m k hr => (h.1 m k hr).symm, h.2.symm⟩

theorem CutEquiv_trans {cx cy cz : Nat → Nat → Bool}
    (h1 : CutEquiv cx cy) (h2 : CutEquiv cy cz) : CutEquiv cx cz :=
  ⟨fun m k hr => (h1.1 m k hr).trans (h2.1 m k hr),
   h1.2.trans h2.2⟩

/-! ## §3 — Unary morphism: `respects ≈` functions -/

/-- A **unary cut morphism**: function on cuts that respects the
    canonical equivalence.  The cut-framework analog of the
    `LensMap` structure from `Padic/SetoidFramework.lean`. -/
structure CutMorphism where
  /-- Underlying function. -/
  fn : (Nat → Nat → Bool) → (Nat → Nat → Bool)
  /-- Respects the canonical equivalence. -/
  respects : ∀ cx cy, CutEquiv cx cy → CutEquiv (fn cx) (fn cy)

/-- Identity is a cut morphism. -/
def CutMorphism.idM : CutMorphism where
  fn := fun c => c
  respects := fun _ _ h => h

/-- Composition of cut morphisms. -/
def CutMorphism.comp (f g : CutMorphism) : CutMorphism where
  fn := fun c => f.fn (g.fn c)
  respects := fun _ _ h => f.respects _ _ (g.respects _ _ h)

/-! ## §4 — Binary morphism + framework algebra instances -/

/-- A **binary cut morphism**: bilinear-respects map. -/
structure CutBinaryMorphism where
  /-- Underlying function. -/
  fn : (Nat → Nat → Bool) → (Nat → Nat → Bool) → (Nat → Nat → Bool)
  /-- Respects the canonical equivalence in both arguments. -/
  respects : ∀ cx cx' cy cy',
              CutEquiv cx cx' → CutEquiv cy cy' →
              CutEquiv (fn cx cy) (fn cx' cy')

/-- Helper: extract pointwise cutEq from CutEquiv. -/
private theorem cutEq_of_CutEquiv {cx cy : Nat → Nat → Bool}
    (h : CutEquiv cx cy) : cutEq cx cy :=
  (CutEquiv_iff_cutEq cx cy).mp h

/-- Helper: lift cutEq to CutEquiv. -/
private theorem CutEquiv_of_cutEq {cx cy : Nat → Nat → Bool}
    (h : cutEq cx cy) : CutEquiv cx cy :=
  (CutEquiv_iff_cutEq cx cy).mpr h

/-- ★★★ **`cutSumN N` is a binary cut morphism**: bilinear
    Stern-Brocot congruence.  Wave 13's `cutSumN N` algebra is
    therefore the canonical setoid's addition operation. -/
def cutSumN_morphism (N : Nat) : CutBinaryMorphism where
  fn := cutSumN N
  respects := fun cx cx' cy cy' hx hy => by
    apply CutEquiv_of_cutEq
    intro m k
    have h1 := cutSumN_cutEq_left N cx cx' cy
                  (cutEq_of_CutEquiv hx) m k
    have h2 := cutSumN_cutEq_right N cx' cy cy'
                  (cutEq_of_CutEquiv hy) m k
    exact h1.trans h2

/-- ★★ **`cutMul` is a binary cut morphism**: routed via the
    existing `cutMul_cutEq_both`. -/
def cutMul_morphism : CutBinaryMorphism where
  fn := cutMul
  respects := fun cx cx' cy cy' hx hy => by
    apply CutEquiv_of_cutEq
    intro m k
    exact cutMul_cutEq_both cx cx' cy cy'
            (cutEq_of_CutEquiv hx) (cutEq_of_CutEquiv hy) m k

/-! ## §5 — Master setoid law

The cut framework respects the canonical equivalence: every
declared operation `cutSumN N`, `cutMul`, and their identity /
composition combinators is a cut morphism. -/

/-- ★★★★★ **Canonical setoid law (master)**: the cut framework
    is closed under the canonical equivalence — bundled as the
    statement that the framework's two binary operations
    (`cutSumN N`, `cutMul`) and the identity/composition unary
    closure are `CutMorphism` / `CutBinaryMorphism` instances. -/
theorem canonical_setoid_law :
    -- (a) Unary identity respects equivalence
    (∀ cx cy, CutEquiv cx cy → CutEquiv (CutMorphism.idM.fn cx) (CutMorphism.idM.fn cy))
    -- (b) cutSumN N is bilinear morphism for every N
    ∧ (∀ N cx cx' cy cy',
        CutEquiv cx cx' → CutEquiv cy cy' →
        CutEquiv (cutSumN N cx cy) (cutSumN N cx' cy'))
    -- (c) cutMul is bilinear morphism
    ∧ (∀ cx cx' cy cy',
        CutEquiv cx cx' → CutEquiv cy cy' →
        CutEquiv (cutMul cx cy) (cutMul cx' cy'))
    -- (d) Composition of unary morphisms respects equivalence
    ∧ (∀ (f g : CutMorphism) cx cy,
        CutEquiv cx cy → CutEquiv ((f.comp g).fn cx) ((f.comp g).fn cy)) :=
  ⟨CutMorphism.idM.respects,
   fun N => (cutSumN_morphism N).respects,
   cutMul_morphism.respects,
   fun f g _ _ h => (f.comp g).respects _ _ h⟩

end E213.Lib.Math.NumberSystems.Real213.Mobius213CutSetoid
