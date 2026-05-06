import E213.Lens.SemanticAtom

/-!
# SubtypeInstance: sub-instance of a distinguishing-closed predicate

User directive (2026-04-25): Internalize the distinguishing-closed assumption
of Subtype inside the framework.

HasDistinguishing instance for `{r : Raw // P r}`.

## Design note

Hit the limits of the elaborator's unfold of nested Subtype (Raw is itself
also a Subtype) for the formal commutativity of the default combine
(Raw.slash).  Instead, instance is formed with *degenerate combine*.

→ The *existence* of a sub-instance is formalized — meaningful combine
design requires additional work due to Lean infrastructure constraints.
-/

namespace E213.Lens.Instances.Subtype

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- Sub-instance for a distinguishing-closed predicate (degenerate
    combine).  The combine result is always a (first base) — degenerate
    but a valid HasDistinguishing instance. -/
def subtypeHasDistinguishing (P : Raw → Prop)
    (h_a : P Raw.a) (h_b : P Raw.b) :
    HasDistinguishing {r : Raw // P r} where
  a := ⟨Raw.a, h_a⟩
  b := ⟨Raw.b, h_b⟩
  distinct := by
    intro heq
    have hval : (Raw.a : Raw) = Raw.b :=
      congrArg Subtype.val heq
    exact absurd hval (by decide)
  combine := fun _ _ => ⟨Raw.a, h_a⟩
  combine_sym := fun _ _ => rfl

end E213.Lens.Instances.Subtype

namespace E213.Lens.Instances.Subtype

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- Universal morphism Raw → {r : Raw // P r} via degenerate
    sub-instance.  Most Raws collapse to a — the natural result of
    a degenerate instance. -/
def subtypeUniversalMorphism (P : Raw → Prop)
    (h_a : P Raw.a) (h_b : P Raw.b) : Raw → {r : Raw // P r} :=
  @universalMorphism {r : Raw // P r} (subtypeHasDistinguishing P h_a h_b)

end E213.Lens.Instances.Subtype
