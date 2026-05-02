import E213.Firmware.Raw.Swap
import E213.Firmware.Raw.Slash

/-!
# Firmware.Raw.Rec: `@[elab_as_elim] Raw.rec`

Custom induction principle for Raw that destructures a canonical
Raw term through three cases — `a`, `b`, `slash x y h ihx ihy` —
with no Tree-level exposure required at use-sites.

Introduced in Phase C3.  Raw-level induction is the intended
way to reason about Raw values in Hypervisor / OS / App; client
code writes `induction r using Raw.rec with | a | b | slash …`.

**WARNING — axiom compliance (AXIOM.md §3)**: the order of the `(x, y)`
pair passed to the slash branch of `Raw.rec` comes from canonical form
— i.e., `Tree.cmp x.val y.val = .lt`.  If the user **treats `x` and
`y` asymmetrically** in that branch (e.g., `f x ≠ f y` is not
covariant under swap), the result depends on an encoding artifact (the
cmp choice).  Every motive value in the slash branch must be invariant
under swapping x and y.  `AUDIT_Lean.md` §5.2(B).

Note: Lean 4 core has `@[elab_as_elim]` but not `@[eliminator]`
(the latter is Mathlib only); `using Raw.rec` is therefore
required — plain `induction r` falls back to the default
`Subtype.mk` eliminator.
-/

namespace E213.Firmware

open E213.Firmware.Internal

-- Private helper: structural recursion on the underlying Tree,
-- re-assembled into Raw at the slash branch.  `noncomputable`
-- since this is a proof-level eliminator, not an executable.
private noncomputable def Raw.recAux {motive : Raw → Sort u}
    (a : motive Raw.a)
    (b : motive Raw.b)
    (slash : ∀ (x y : Raw) (h : x ≠ y),
                  motive x → motive y →
                  motive (Raw.slash x y h)) :
    ∀ (t : Tree) (hcanon : t.canonical = true), motive ⟨t, hcanon⟩ := by
  intro t
  induction t with
  | a => intro _; exact a
  | b => intro _; exact b
  | slash x y ihx ihy =>
      intro hcanon
      have hc := hcanon
      unfold Tree.canonical at hc
      obtain ⟨hxy, _⟩ := Bool.and_eq_true_to_pair hc
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy
      have hcmp := Tree.canonical_slash_lt hcanon
      let x' : Raw := ⟨x, hx⟩
      let y' : Raw := ⟨y, hy⟩
      have hne : x' ≠ y' := by
        intro heq
        have hxy : x = y := congrArg Subtype.val heq
        rw [hxy] at hcmp
        rw [Tree.cmp_self_eq y] at hcmp
        cases hcmp
      have heq : (⟨.slash x y, hcanon⟩ : Raw) = Raw.slash x' y' hne := by
        show (⟨.slash x y, hcanon⟩ : Raw) = Raw.slash ⟨x, hx⟩ ⟨y, hy⟩ hne
        unfold Raw.slash
        split <;> rename_i hc
        · rfl
        · rw [hcmp] at hc; cases hc
        · rw [hcmp] at hc; cases hc
      rw [heq]
      exact slash x' y' hne (ihx hx) (ihy hy)

/-- Custom Raw eliminator — use as `induction r using Raw.rec`.
    (`@[eliminator]` attribute is Mathlib-only; we register via
    `elab_as_elim` so the elaborator treats it correctly in
    `induction`-style tactic applications.) -/
@[elab_as_elim]
noncomputable def Raw.rec {motive : Raw → Sort u}
    (a : motive Raw.a)
    (b : motive Raw.b)
    (slash : ∀ (x y : Raw) (h : x ≠ y),
                  motive x → motive y →
                  motive (Raw.slash x y h))
    (r : Raw) : motive r :=
  Raw.recAux a b slash r.val r.property

end E213.Firmware
