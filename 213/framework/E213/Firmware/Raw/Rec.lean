import E213.Firmware.Raw.Swap
import E213.Firmware.Raw.Slash

/-!
# Firmware.Raw.Rec: `@[eliminator] Raw.rec`

Custom induction principle for Raw that destructures a canonical
Raw term through three cases — `a`, `b`, `slash x y h ihx ihy` —
with no Tree-level exposure required at use-sites.

Introduced in Phase C3.  Raw-level induction is the intended
way to reason about Raw values in Hypervisor / OS / App.
-/

namespace E213.Firmware

open E213.Firmware.Internal

-- Private helper: structural recursion on the underlying Tree,
-- re-assembled into Raw at the slash branch.  `noncomputable`
-- since this is a proof-level eliminator, not an executable.
private noncomputable def Raw.recAux {motive : Raw → Sort u}
    (a_case : motive Raw.a)
    (b_case : motive Raw.b)
    (slash_case : ∀ (x y : Raw) (h : x ≠ y),
                  motive x → motive y →
                  motive (Raw.slash x y h)) :
    ∀ (t : Tree) (hcanon : t.canonical = true), motive ⟨t, hcanon⟩ := by
  intro t
  induction t with
  | a => intro _; exact a_case
  | b => intro _; exact b_case
  | slash x y ihx ihy =>
      intro hcanon
      have hc := hcanon
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hcmp := Tree.canonical_slash_lt hcanon
      let x' : Raw := ⟨x, hx⟩
      let y' : Raw := ⟨y, hy⟩
      have hne : x' ≠ y' := by
        intro heq
        have hxy : x = y := congrArg Subtype.val heq
        rw [hxy] at hcmp
        rw [(Tree.cmp_eq_iff y y).mpr rfl] at hcmp
        cases hcmp
      have heq : (⟨.slash x y, hcanon⟩ : Raw) = Raw.slash x' y' hne := by
        show (⟨.slash x y, hcanon⟩ : Raw) = Raw.slash ⟨x, hx⟩ ⟨y, hy⟩ hne
        unfold Raw.slash
        split <;> rename_i hc
        · rfl
        · rw [hcmp] at hc; cases hc
        · rw [hcmp] at hc; cases hc
      rw [heq]
      exact slash_case x' y' hne (ihx hx) (ihy hy)

/-- Custom Raw eliminator — use as `induction r using Raw.rec`.
    (`@[eliminator]` attribute is Mathlib-only; we register via
    `elab_as_elim` so the elaborator treats it correctly in
    `induction`-style tactic applications.) -/
@[elab_as_elim]
noncomputable def Raw.rec {motive : Raw → Sort u}
    (a_case : motive Raw.a)
    (b_case : motive Raw.b)
    (slash_case : ∀ (x y : Raw) (h : x ≠ y),
                  motive x → motive y →
                  motive (Raw.slash x y h))
    (r : Raw) : motive r :=
  Raw.recAux a_case b_case slash_case r.val r.property

end E213.Firmware
