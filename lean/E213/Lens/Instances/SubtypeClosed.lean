import E213.Lens.SemanticAtom

/-!
# SubtypeInstanceClosed: slash-based combine instance for
distinguishing-closed subtype

Fix for the third closed-subtype boundary: bypasses the nested-Subtype
elaborator via SlashClosed typeclass + decidable equality on Raw.

## Core

`SlashClosed P`: carries as data that P is closed over distinct slash arguments.
Under this assumption, the slash-based combine on `{r : Raw // P r}` is
well-defined + commutative.

Replaces the degenerate combine of `SubtypeInstance.lean`.
-/

namespace E213.Lens.Instances.SubtypeClosed

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- `P` is closed over `Raw.slash`: P is preserved on distinct args. -/
class SlashClosed (P : Raw → Prop) : Prop where
  closed : ∀ {x y : Raw} (h : x ≠ y), P x → P y → P (Raw.slash x y h)


/-- Slash-based combine on Subtype.  Falls back to base_a when
    vals are equal (since slash only accepts distinct args). -/
def subtypeCombine (P : Raw → Prop) [SlashClosed P]
    (h_a : P Raw.a) :
    {r : Raw // P r} → {r : Raw // P r} → {r : Raw // P r} :=
  fun x y =>
    if h : x.val = y.val then ⟨Raw.a, h_a⟩
    else ⟨Raw.slash x.val y.val h,
          SlashClosed.closed h x.property y.property⟩

theorem subtypeCombine_comm (P : Raw → Prop) [SlashClosed P]
    (h_a : P Raw.a) (x y : {r : Raw // P r}) :
    subtypeCombine P h_a x y = subtypeCombine P h_a y x := by
  unfold subtypeCombine
  by_cases h : x.val = y.val
  · have hsym : y.val = x.val := h.symm
    rw [dif_pos h, dif_pos hsym]
  · have hsym : y.val ≠ x.val := fun e => h e.symm
    rw [dif_neg h, dif_neg hsym]
    apply Subtype.ext
    exact Raw.slash_comm _ _ h


/-- **Slash-based HasDistinguishing instance** on
    `{r : Raw // P r}` for distinguishing-closed `P`.
    The *meaningful* version of the degenerate combine in
    `SubtypeInstance.lean`.  The third closed-subtype boundary is
    resolved with the SlashClosed typeclass. -/
def subtypeHasDistinguishingClosed (P : Raw → Prop) [SlashClosed P]
    (h_a : P Raw.a) (h_b : P Raw.b) :
    HasDistinguishing {r : Raw // P r} where
  a := ⟨Raw.a, h_a⟩
  b := ⟨Raw.b, h_b⟩
  distinct := by
    intro heq
    have hval : (Raw.a : Raw) = Raw.b := congrArg Subtype.val heq
    exact absurd hval (by decide)
  combine := subtypeCombine P h_a
  combine_sym := subtypeCombine_comm P h_a


/-! ### Concrete instance: `True`-predicate (the trivial slash-closed)

`P := fun _ => True` is trivially SlashClosed.  The resulting subtype
`{r : Raw // True}` is isomorphic to Raw, and the instance on it
uses slash-based combine. -/

instance trueSlashClosed : SlashClosed (fun _ => True) where
  closed := fun _ _ _ => trivial

/-- Slash-based instance on `{r : Raw // True}`.  Essentially
    equivalent to the instance of `Raw` itself — meaningful combine. -/
def trueSubtypeInstance : HasDistinguishing {r : Raw // True} :=
  subtypeHasDistinguishingClosed (fun _ => True) trivial trivial

end E213.Lens.Instances.SubtypeClosed
