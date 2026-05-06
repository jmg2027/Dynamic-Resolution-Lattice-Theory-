import E213.Lens.LensCore
import E213.Lens.Compose.Factoring

/-!
# LeavesMod3: leaves count mod 3 Lens

**Lens**: `leavesMod3Lens : Lens (Fin 3)` observes leaves count mod 3.

This provides an additional natural Lens kernel beyond parity (mod 2)
— in general, for every m ≥ 2, "leaves mod m" is a
slash-congruence.  Therefore the Lens kernel has at least countably
infinitely many elements.

## Theorems

- `leavesMod3Lens_view_eq` — view = leaves % 3.
- `leaves_refines_mod3` — Lens.leaves.refines leavesMod3Lens.
- `mod3_distinct_from_parity` (prose): the mod 3 kernel differs from
  the parity kernel (distinguishes leaves 1 vs 3).
-/

namespace E213.Lens.Leaves.Mod3

open E213.Theory E213.Lens E213.Lens.Compose.Factoring

/-- Fin 3 addition (mod 3). -/
private def f3add (a b : Fin 3) : Fin 3 :=
  ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩

/-- Leaves mod 3 Lens. -/
def leavesMod3Lens : Lens (Fin 3) where
  base_a := ⟨1, by decide⟩
  base_b := ⟨1, by decide⟩
  combine := f3add

private theorem f3add_comm (a b : Fin 3) : f3add a b = f3add b a := by
  unfold f3add; congr 1; omega

private theorem f3add_mod (a b : Nat) :
    (a % 3 + b % 3) % 3 = (a + b) % 3 := by
  rw [← Nat.add_mod]

theorem leavesMod3Lens_view_eq :
    ∀ r : Raw, (leavesMod3Lens.view r).val = Lens.leaves.view r % 3 := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfsM : leavesMod3Lens.view (Raw.slash x y h)
                    = f3add (leavesMod3Lens.view x) (leavesMod3Lens.view y) :=
        Raw.fold_slash _ _ _ f3add_comm x y h
      have hfsN : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsM, hfsN]
      unfold f3add
      simp only [Fin.val_mk]
      rw [ihx, ihy, f3add_mod]

end E213.Lens.Leaves.Mod3

namespace E213.Lens.Leaves.Mod3

open E213.Theory E213.Lens E213.Lens.Compose.Factoring

/-- Factor function: leaves count → Fin 3. -/
private def mod3Factor (n : Nat) : Fin 3 :=
  ⟨n % 3, Nat.mod_lt _ (by decide)⟩

/-- leaves refines mod 3. -/
theorem leaves_refines_mod3 : Lens.leaves.refines leavesMod3Lens := by
  apply refines_of_factor Lens.leaves leavesMod3Lens mod3Factor
  intro r
  apply Fin.ext
  exact leavesMod3Lens_view_eq r

end E213.Lens.Leaves.Mod3
