import E213.Lens.Universal

/-!
# ChoiceResolved: Formal version of "choice = Lens specification"

Explicit formalization of the thesis in Note 44:

**For any slash-congruence E, a concrete Lens exists**.
Without Classical.choice or any external axiom.

This is the precise meaning of "choice reduces to Lens spec" inside 213.
Not an abstract choice function, but an explicit Lens specified by the
universalLens construction.

## Theorem

`choice_as_lens_spec`: ∀ E (equiv + slash-cong), ∃ L : Lens
  (Raw → Prop), ∀ r r', L.equivR r r' ↔ E r r'.

Proof: ⟨universalLens E, universalLens_kernel_eq_E_R E ...⟩.

0 external axioms.  Constructive existence — explicit witness
universalLens E.
-/

namespace E213.Lib.Math.Choice.Resolved

open E213.Theory E213.Lens E213.Lens.Universal.QuotLens

/-- **Choice resolved**: For any slash-congruence E, a concrete Lens
    exists (0 external axioms).  Universal construction without
    Classical.choice.  The specification is the Reading-equivalence kernel
    (`equivR`), so the existence is ∅-axiom — no `funext`/`propext`. -/
theorem choice_as_lens_spec (E : Raw → Raw → Prop)
    (hrefl : ∀ r, E r r)
    (hsymm : ∀ r r', E r r' → E r' r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h')) :
    ∃ L : Lens (Raw → Prop),
      ∀ r r' : Raw, L.equivR r r' ↔ E r r' :=
  ⟨universalLens E,
   fun r r' => universalLens_kernel_eq_E_R E hrefl hsymm htrans hslash r r'⟩

/-- **Choice as a direct consequence of Lens instances**: for each
    slash-cong E, universalLens E is the explicit witness of that choice. -/
def witness_explicit (E : Raw → Raw → Prop) :
    Lens (Raw → Prop) := universalLens E

end E213.Lib.Math.Choice.Resolved
