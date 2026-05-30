import E213.Lens.FlatOntology
import E213.Lens.Cardinality.Cantor

/-!
# Lens.FlatOntologyClosure — the self-covering closure, exactly up to the residue

`FlatOntology` realises every sort (object / type / relation / function / Lens)
as one primitive: a decidable predicate on `Raw^n`.  It defers the *closure*
direction — encoding a predicate back as a Raw (`seed/AXIOM/06_lens_readings.md`
§6.3; `research-notes/G29_residue.md` "자기-덮음").

This file records the 213-native shape of that closure:

  * **Faithful**: `Object1 : Raw → (Raw → Bool)` (each Raw as its own indicator
    `· = r`) is **injective** — Raw self-covers as predicates with nothing lost.
  * **Not total**: `Object1` is **not surjective** — the predicates *not* of the
    form `· = r` are exactly the Cantor-unpointable surplus
    (`Cardinality.cantor_raw_bool`).  That surplus is the **residue**: the part
    of the predicate algebra the substrate cannot point at as a single Raw.

So the self-covering "closes exactly up to the residue": faithful on what can be
pointed at, with the unpointable surplus being the residue itself.  This is the
∅-axiom statement of the session thesis (`research-notes/G152_...`): pointing is
finite; the completed-infinite surplus is a finite *name*, not an inhabitant.
-/

namespace E213.Lens.FlatOntologyClosure

open E213.Theory (Raw)
open E213.Lens.FlatOntology (Object1)

/-- The self-cover `Object1` is **injective**: distinct Raws give distinct
    indicator predicates.  Faithful self-covering — applying both sides at `r`
    forces `decide (r = s) = true`, hence `r = s`. -/
theorem object1_injective : Function.Injective Object1 := by
  intro r s h
  -- `h : Object1 r = Object1 s`; evaluate both sides at `r`.
  have hr : Object1 r r = Object1 s r := congrFun h r
  -- `Object1 r r = true`, so `Object1 s r = true`, i.e. `decide (r = s) = true`.
  rw [E213.Lens.FlatOntology.Object1_self] at hr
  -- `Object1 s r = decide (r = s)`; from `true = decide (r = s)` get `r = s`.
  exact decide_eq_true_eq.mp hr.symm

/-- The self-cover `Object1` is **not surjective**: there is no surjection
    `Raw → (Raw → Bool)` at all (Cantor).  The predicates outside the image of
    `Object1` are the residue surplus. -/
theorem object1_not_surjective : ¬ Function.Surjective Object1 :=
  fun hsurj => E213.Lens.Cardinality.cantor_raw_bool ⟨Object1, hsurj⟩

/-- ★ **Self-covering closure capstone.**  The flat-ontology self-cover
    `Object1 : Raw → (Raw → Bool)` is faithful (injective) but not total
    (not surjective).  Raw embeds exactly into its own predicate algebra, and
    the un-embedded surplus — the Cantor-unpointable predicates — is the
    residue. -/
theorem self_covering_closure :
    Function.Injective Object1 ∧ ¬ Function.Surjective Object1 :=
  ⟨object1_injective, object1_not_surjective⟩

end E213.Lens.FlatOntologyClosure
