import E213.Lens.Lattice.JoinEquiv
import E213.Lens.Algebra.Congruence
import E213.Lens.Instances.Parity
import E213.Lens.Instances.Bool

/-!
# ParityXorJoin: parityLens ⊔ boolXorLens = constant

The first concrete example of a join for a non-mod family pair.

parityLens and boolXorLens are incomparable (`ParityXorIncomparable`),
but their **join in the refines preorder is universal**:

    JoinEquiv parityLens boolXorLens r r'  (for arbitrary r, r')

That is, every Lens refining both is constant.

## Proof structure

Show JoinEquiv r Raw.a for every r (then use trans + symm).

Case analysis on (parityLens.view r, boolXorLens.view r):
- (T, T): boolXorLens.equiv r Raw.a → ofM
- (T, F): parityLens.equiv r Raw.a → ofL
- (F, T): boolXorLens.equiv r Raw.a → ofM
- (F, F): chain via Raw.b (r ~_boolXor Raw.b ~_parity Raw.a)
-/

namespace E213.Lens.Instances.ParityXorJoin

open E213.Firmware E213.Lens E213.Meta E213.Lens.Lattice.JoinEquiv

private theorem join_to_a (r : Raw) :
    JoinEquiv parityLens boolXorLens r Raw.a := by
  rcases hp : parityLens.view r with _ | _
  all_goals rcases hb : boolXorLens.view r with _ | _
  · -- (F, F): chain via Raw.b
    have h_rb_boolXor : boolXorLens.equiv r Raw.b := by
      show boolXorLens.view r = boolXorLens.view Raw.b
      rw [hb]; rfl
    have h_ba_parity : parityLens.equiv Raw.b Raw.a := by
      show parityLens.view Raw.b = parityLens.view Raw.a
      rfl
    exact JoinEquiv.trans (JoinEquiv.ofM h_rb_boolXor) (JoinEquiv.ofL h_ba_parity)
  · -- (F, T): boolXorLens.equiv r Raw.a (both true)
    apply JoinEquiv.ofM
    show boolXorLens.view r = boolXorLens.view Raw.a
    rw [hb]; rfl
  · -- (T, F): parityLens.equiv r Raw.a (both true)
    apply JoinEquiv.ofL
    show parityLens.view r = parityLens.view Raw.a
    rw [hp]; rfl
  · -- (T, T): boolXorLens.equiv r Raw.a
    apply JoinEquiv.ofM
    show boolXorLens.view r = boolXorLens.view Raw.a
    rw [hb]; rfl

/-- **Join is universal**: JoinEquiv parityLens boolXorLens r r' for
    arbitrary r, r'.  Hence any N refining both is constant. -/
theorem joinEquiv_parityLens_boolXorLens_universal :
    ∀ r r' : Raw, JoinEquiv parityLens boolXorLens r r' := by
  intro r r'
  exact JoinEquiv.trans (join_to_a r) (JoinEquiv.symm (join_to_a r'))

/-- **Consequence**: any symmetric-combine Lens refining both
    parityLens and boolXorLens is constant.  (Applying
    JoinEquiv_is_least.) -/
theorem refine_parity_boolXor_implies_const {γ : Type} (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLp : parityLens.refines N) (hLb : boolXorLens.refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  exact JoinEquiv_is_least parityLens boolXorLens N hNsym hLp hLb r r'
    (joinEquiv_parityLens_boolXorLens_universal r r')

namespace E213.Lens.Instances.ParityXorJoin

open E213.Firmware E213.Lens E213.Meta E213.Lens.Lattice.JoinEquiv

private theorem leavesLens_to_a (r : Raw) :
    JoinEquiv Lens.leaves boolXorLens r Raw.a := by
  rcases hb : boolXorLens.view r with _ | _
  · -- r's a-parity = even.  Same as Raw.b. Chain via Raw.b.
    have h_rb : boolXorLens.equiv r Raw.b := by
      show boolXorLens.view r = boolXorLens.view Raw.b
      rw [hb]; rfl
    have h_ba_leaves : Lens.leaves.equiv Raw.b Raw.a := by
      show Lens.leaves.view Raw.b = Lens.leaves.view Raw.a
      rfl
    exact JoinEquiv.trans (JoinEquiv.ofM h_rb) (JoinEquiv.ofL h_ba_leaves)
  · -- r's a-parity = odd.  Same as Raw.a. Direct ofM.
    apply JoinEquiv.ofM
    show boolXorLens.view r = boolXorLens.view Raw.a
    rw [hb]; rfl

/-- **leaves ⊔ boolXorLens = universal**.  leaves is a count
    (number of leaves), boolXorLens is the a-parity.  The join of
    the two pieces of information is universal (N constant). -/
theorem joinEquiv_leavesLens_boolXorLens_universal :
    ∀ r r' : Raw, JoinEquiv Lens.leaves boolXorLens r r' := by
  intro r r'
  exact JoinEquiv.trans (leavesLens_to_a r)
    (JoinEquiv.symm (leavesLens_to_a r'))

/-- **Consequence**: any symmetric-combine Lens refining both leaves
    and boolXorLens is constant. -/
theorem refine_leaves_boolXor_implies_const {γ : Type} (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLl : Lens.leaves.refines N) (hLb : boolXorLens.refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  exact JoinEquiv_is_least Lens.leaves boolXorLens N hNsym hLl hLb r r'
    (joinEquiv_leavesLens_boolXorLens_universal r r')

end E213.Lens.Instances.ParityXorJoin
