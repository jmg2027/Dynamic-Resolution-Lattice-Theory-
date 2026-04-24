import E213.Research.JoinEquiv

/-!
# Research.LeavesDepthJoin: leaves ⊔ depth ≠ constLens (비-mod non-trivial join)

`LeavesDepthIncomparable` 에서 leaves 와 depth 가 incomparable 임을
확인.  여기서 둘의 **join 이 universal 이 아님** 을 형식적으로
증명.

## 핵심 관찰

Raw.a (leaves=1, depth=0) 와 Raw.slash Raw.a Raw.b h (leaves=2,
depth=1) 는 JoinEquiv(leaves, depth) 에서 **분리된 class**.

## 증명 전략

Invariant `small r := Lens.leaves.view r = 1` 가 JoinEquiv 하에
preserved.

- ofL (leaves.equiv): same leaves, so same small-ness.
- ofM (depth.equiv): depth=0 ↔ leaves=1 ↔ small, so preserved.
- slash_cong: output 는 항상 Raw.slash (depth ≥ 1, leaves ≥ 2),
  never small.  양쪽 다 ¬ small, invariant holds vacuously.
- refl, symm, trans: 표준.

Raw.a 는 small, Raw.slash Raw.a Raw.b 는 not small.  따라서
JoinEquiv 로 분리.
-/

namespace E213.Research.LeavesDepthJoin

open E213.Firmware E213.Hypervisor E213.Research.JoinEquiv

/-- `small r` := r 가 base (Raw.a 또는 Raw.b), leaves=1. -/
private def small (r : Raw) : Prop := Lens.leaves.view r = 1

private theorem small_of_leaves_one {r : Raw} (h : Lens.leaves.view r = 1) : small r := h

private theorem leaves_of_small {r : Raw} (h : small r) : Lens.leaves.view r = 1 := h

/-- Leaves view 는 항상 ≥ 1. -/
private theorem leaves_ge_one (r : Raw) : 1 ≤ Lens.leaves.view r := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]; omega

/-- Raw.slash x y h 는 leaves ≥ 2 이므로 ¬ small. -/
private theorem not_small_slash (x y : Raw) (h : x ≠ y) :
    ¬ small (Raw.slash x y h) := by
  intro hsmall
  have hfs : Lens.leaves.view (Raw.slash x y h)
               = Lens.leaves.view x + Lens.leaves.view y := by
    apply Raw.fold_slash
    intro u v; exact Nat.add_comm u v
  have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
  have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
  have : Lens.leaves.view (Raw.slash x y h) ≥ 2 := by
    rw [hfs]; omega
  unfold small at hsmall
  omega

/-- Depth=0 iff small (= leaves=1 = base Raw.a/Raw.b). -/
private theorem small_iff_depth_zero (r : Raw) :
    small r ↔ Lens.depth.view r = 0 := by
  induction r using Raw.rec with
  | a => simp [small, Lens.leaves, Lens.depth, Lens.view, Raw.fold_a]
  | b => simp [small, Lens.leaves, Lens.depth, Lens.view, Raw.fold_b]
  | slash x y h _ _ =>
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hfsD : Lens.depth.view (Raw.slash x y h)
                    = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
        apply Raw.fold_slash
        intro u v
        show 1 + max u v = 1 + max v u
        rw [Nat.max_comm]
      have hxge : 1 ≤ Lens.leaves.view x := leaves_ge_one x
      have hyge : 1 ≤ Lens.leaves.view y := leaves_ge_one y
      constructor
      · intro hs
        unfold small at hs
        rw [hfsL] at hs
        omega
      · intro hd
        rw [hfsD] at hd
        omega

/-- **핵심 invariant**: `small r ↔ small r'` under JoinEquiv leaves depth. -/
theorem small_invariant (r r' : Raw)
    (h : JoinEquiv Lens.leaves Lens.depth r r') :
    small r ↔ small r' := by
  induction h with
  | ofL hrr' =>
      -- leaves.equiv: Lens.leaves.view r = Lens.leaves.view r'
      have : Lens.leaves.view _ = Lens.leaves.view _ := hrr'
      unfold small
      rw [this]
  | ofM hrr' =>
      have : Lens.depth.view _ = Lens.depth.view _ := hrr'
      rw [small_iff_depth_zero, small_iff_depth_zero, this]
  | refl x => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | slash_cong hxy hx'y' _ _ _ _ =>
      constructor
      · intro hs; exact absurd hs (not_small_slash _ _ hxy)
      · intro hs; exact absurd hs (not_small_slash _ _ hx'y')

/-- **Main 결과**: leaves ⊔ depth ≠ constLens (universal).
    Raw.a (leaves=1) 와 Raw.slash Raw.a Raw.b (leaves=2) 는
    JoinEquiv 분리.  즉 두 Lens 의 join 은 non-universal.  따라서
    비-mod family non-trivial (non-const) join 존재. -/
theorem leaves_depth_join_not_universal :
    ¬ JoinEquiv Lens.leaves Lens.depth Raw.a
        (Raw.slash Raw.a Raw.b (by decide)) := by
  intro h
  have := (small_invariant _ _ h).mp (by unfold small; rfl)
  exact not_small_slash _ _ _ this

end E213.Research.LeavesDepthJoin
