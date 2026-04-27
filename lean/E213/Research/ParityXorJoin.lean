import E213.Research.JoinEquiv
import E213.Research.KernelCongruence
import E213.Meta.ParityLens
import E213.Meta.BoolLens

/-!
# Research.ParityXorJoin: parityLens ⊔ boolXorLens = constant

비-mod family pair 에 대한 concrete join 의 첫 예시.

parityLens 와 boolXorLens 는 incomparable (`ParityXorIncomparable`)
이지만, refines preorder 에서 **join 은 universal**:

    JoinEquiv parityLens boolXorLens r r'  (임의 r, r')

즉 둘 모두를 refine 하는 Lens 는 전부 constant.

## 증명 구조

모든 r 에 대해 JoinEquiv r Raw.a 를 show (then trans + symm).

(parityLens.view r, boolXorLens.view r) 의 4 케이스 분석:
- (T, T): boolXorLens.equiv r Raw.a → ofM
- (T, F): parityLens.equiv r Raw.a → ofL
- (F, T): boolXorLens.equiv r Raw.a → ofM
- (F, F): chain via Raw.b (r ~_boolXor Raw.b ~_parity Raw.a)
-/

namespace E213.Research.ParityXorJoin

open E213.Firmware E213.Hypervisor E213.Meta E213.Research.JoinEquiv

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

/-- **Join 이 universal**: 임의 r, r' 에 대해 JoinEquiv parityLens
    boolXorLens r r'.  즉 둘을 refine 하는 N 은 constant. -/
theorem joinEquiv_parityLens_boolXorLens_universal :
    ∀ r r' : Raw, JoinEquiv parityLens boolXorLens r r' := by
  intro r r'
  exact JoinEquiv.trans (join_to_a r) (JoinEquiv.symm (join_to_a r'))

/-- **귀결**: parityLens 와 boolXorLens 를 모두 refine 하는
    symmetric-combine Lens 는 constant.  (JoinEquiv_is_least
    적용.) -/
theorem refine_parity_boolXor_implies_const {γ : Type} (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLp : parityLens.refines N) (hLb : boolXorLens.refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  exact JoinEquiv_is_least parityLens boolXorLens N hNsym hLp hLb r r'
    (joinEquiv_parityLens_boolXorLens_universal r r')

namespace E213.Research.ParityXorJoin

open E213.Firmware E213.Hypervisor E213.Meta E213.Research.JoinEquiv

private theorem leavesLens_to_a (r : Raw) :
    JoinEquiv Lens.leaves boolXorLens r Raw.a := by
  rcases hb : boolXorLens.view r with _ | _
  · -- r 의 a-parity = even.  Raw.b 와 같음. Chain via Raw.b.
    have h_rb : boolXorLens.equiv r Raw.b := by
      show boolXorLens.view r = boolXorLens.view Raw.b
      rw [hb]; rfl
    have h_ba_leaves : Lens.leaves.equiv Raw.b Raw.a := by
      show Lens.leaves.view Raw.b = Lens.leaves.view Raw.a
      rfl
    exact JoinEquiv.trans (JoinEquiv.ofM h_rb) (JoinEquiv.ofL h_ba_leaves)
  · -- r 의 a-parity = odd.  Raw.a 와 같음. ofM 직접.
    apply JoinEquiv.ofM
    show boolXorLens.view r = boolXorLens.view Raw.a
    rw [hb]; rfl

/-- **leaves ⊔ boolXorLens = universal**.  leaves 는 카운트
    (leaf 수), boolXorLens 는 a-parity.  두 정보의 join 은
    universal (N constant). -/
theorem joinEquiv_leavesLens_boolXorLens_universal :
    ∀ r r' : Raw, JoinEquiv Lens.leaves boolXorLens r r' := by
  intro r r'
  exact JoinEquiv.trans (leavesLens_to_a r)
    (JoinEquiv.symm (leavesLens_to_a r'))

/-- **귀결**: leaves 와 boolXorLens 모두 refine 하는 symmetric-
    combine Lens 는 constant. -/
theorem refine_leaves_boolXor_implies_const {γ : Type} (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLl : Lens.leaves.refines N) (hLb : boolXorLens.refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  intro r r'
  exact JoinEquiv_is_least Lens.leaves boolXorLens N hNsym hLl hLb r r'
    (joinEquiv_leavesLens_boolXorLens_universal r r')

end E213.Research.ParityXorJoin
