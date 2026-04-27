import E213.Research.IdentityLens
import E213.Research.LensMeet

/-!
# Research.ProdBelowId: Q39.2 의 witness

`prodLens Lens.leaves Lens.depth ⊏ idLens` 엄격.  즉 (leaves,
depth) 쌍이 같지만 구별되는 Raw 원소가 존재.

Witness:
- `rA` := `a / (a / (a/b))` — leaves=4, depth=3.
- `rB` := `a / (b / (a/b))` — leaves=4, depth=3.
- `rA ≠ rB` (inner slash 의 왼쪽이 a vs b 로 다름).

(leaves, depth) 로는 구별 불가, idLens 로는 구별 가능.
-/

namespace E213.Research.ProdBelowId

open E213.Firmware E213.Hypervisor
open E213.Research.IdentityLens E213.Research.LensMeet

/-- Witness A: `a / (a / (a/b))`. -/
def rA : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

/-- Witness B: `a / (b / (a/b))`. -/
def rB : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

theorem rA_ne_rB : rA ≠ rB := by decide

theorem leaves_equal : Lens.leaves.view rA = Lens.leaves.view rB := by decide

theorem depth_equal : Lens.depth.view rA = Lens.depth.view rB := by decide

private theorem leaves_sym : ∀ u v : Nat, u + v = v + u := Nat.add_comm

private theorem depth_sym :
    ∀ u v : Nat, 1 + max u v = 1 + max v u := by
  intro u v; rw [Nat.max_comm]

/-- prod of (leaves, depth) equates rA and rB. -/
theorem prod_equates :
    (prodLens Lens.leaves Lens.depth).view rA
      = (prodLens Lens.leaves Lens.depth).view rB := by
  rw [prodLens_view _ _ leaves_sym depth_sym,
      prodLens_view _ _ leaves_sym depth_sym,
      leaves_equal, depth_equal]

/-- **idLens distinguishes them** (they are unequal Raw). -/
theorem idLens_distinguishes : idLens.view rA ≠ idLens.view rB := by
  rw [idLens_is_id, idLens_is_id]
  exact rA_ne_rB

/-- **Strict refinement**: prodLens (leaves, depth) 는 idLens 를
    refine 하지 않음 (prod 로 구별 안 되는 쌍이 idLens 로는
    구별됨).  즉 prod 의 kernel 이 idLens 의 kernel 보다 엄격히
    큼 → prod ⊏ idLens 하지만 prod ≠ idLens. -/
theorem prod_not_refines_idLens :
    ¬ (prodLens Lens.leaves Lens.depth).refines idLens := by
  intro h
  exact idLens_distinguishes (h rA rB prod_equates)

end E213.Research.ProdBelowId
