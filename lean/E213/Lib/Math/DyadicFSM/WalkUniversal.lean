import E213.Lib.Math.DyadicFSM.Conjecture

/-!
# K_{3,2}^{(2)} bit-walk universality — chooseEdge witness

Strong form of Conjecture 2: every Bool sequence is realisable as
a K_{3,2}^{(2)} bit-walk.  Every vertex has both bits 0 and 1 in
its incident edges, so a walk can always be extended.

Implication: Conjecture 2 holds *trivially* in the existence form;
the non-trivial content must be that the walk is *canonical* /
*signature-bearing*, not merely existent.

This file gives the constructive selector `chooseEdge : Fin 5 →
Bool → Fin 12` that, at each (vertex, bit), names a specific
edge.  Full universality (∀ bs : List Bool, ∃ walk ...) requires
walk-construction by induction; deferred while the canonicity
question is open.
-/

namespace E213.Lib.Math.DyadicFSM.WalkUniversal

/-- Constructive edge selector by `v.val`. -/
def chooseEdge (v : Fin 5) (b : Bool) : Fin 12 :=
  match h : v.val with
  | 0 => bif b then ⟨1, by decide⟩ else ⟨0, by decide⟩
  | 1 => bif b then ⟨5, by decide⟩ else ⟨4, by decide⟩
  | 2 => bif b then ⟨9, by decide⟩ else ⟨8, by decide⟩
  | 3 => bif b then ⟨1, by decide⟩ else ⟨0, by decide⟩
  | 4 => bif b then ⟨3, by decide⟩ else ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

/-- chooseEdge yields the requested bit at each concrete vertex. -/
theorem chooseEdge_bit_smoke :
    ((chooseEdge ⟨0, by decide⟩ true).val % 2 == 1) = true
    ∧ ((chooseEdge ⟨1, by decide⟩ false).val % 2 == 1) = false
    ∧ ((chooseEdge ⟨4, by decide⟩ true).val % 2 == 1) = true
    ∧ ((chooseEdge ⟨3, by decide⟩ false).val % 2 == 1) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- ★ All 10 vertex+bit cases bundled. -/
theorem chooseEdge_bit_full :
    (∀ b : Bool, ((chooseEdge ⟨0, by decide⟩ b).val % 2 == 1) = b)
    ∧ (∀ b : Bool, ((chooseEdge ⟨1, by decide⟩ b).val % 2 == 1) = b)
    ∧ (∀ b : Bool, ((chooseEdge ⟨2, by decide⟩ b).val % 2 == 1) = b)
    ∧ (∀ b : Bool, ((chooseEdge ⟨3, by decide⟩ b).val % 2 == 1) = b)
    ∧ (∀ b : Bool, ((chooseEdge ⟨4, by decide⟩ b).val % 2 == 1) = b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro b <;> cases b <;> rfl

end E213.Lib.Math.DyadicFSM.WalkUniversal
