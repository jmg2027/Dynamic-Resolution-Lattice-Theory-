/-
  PmfRh/ScaleConfluence.lean

  Formalization of Claim 2' from FND_032:
    For a refinement operator R on states, the following are
    EQUIVALENT:
      (i)  R is confluent (Church-Rosser)
      (ii) R has at most one normal form per orbit (uniqueness)

  Scale-invariance interpretation: normal form = limit of refinement.
  Confluent refinement has unique limit up to equivalence.
  Hence Confluence ⟺ unique scale-invariant limit.

  SCOPE (precise):
    PROVEN: abstract theorem on rewriting relations.
    PREMISES: reflexive-transitive closure machinery from Mathlib.
    INTERPRETATIONS (not in Lean):
      "Scale invariance" = normal form = R-fixed.
      Geometric meaning (γ on simplicial complexes, fractals) is
      outside this abstract file.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import Mathlib.Logic.Relation
import Mathlib.Tactic

set_option autoImplicit false

namespace DRLT.Foundation.Claim2

/-! ## Setup: abstract rewriting -/

variable {α : Type*}

/-- Normal form: x has no R-successor. -/
def IsNormal (R : α → α → Prop) (x : α) : Prop :=
  ∀ y, ¬ R x y

/-- Confluent: any two reductions from x reach a common successor. -/
def IsConfluent (R : α → α → Prop) : Prop :=
  ∀ x y z, Relation.ReflTransGen R x y → Relation.ReflTransGen R x z →
    ∃ w, Relation.ReflTransGen R y w ∧ Relation.ReflTransGen R z w

/-! ## Direction 1: Confluence ⟹ unique normal form -/

/-- If R is confluent, then every state reduces to AT MOST ONE normal form.
    This is the "uniqueness" side of Claim 2'. -/
theorem confluent_implies_unique_normal
    {R : α → α → Prop} (hc : IsConfluent R) :
    ∀ x y z, Relation.ReflTransGen R x y →
             Relation.ReflTransGen R x z →
             IsNormal R y → IsNormal R z → y = z := by
  intro x y z hxy hxz hy hz
  obtain ⟨w, hyw, hzw⟩ := hc x y z hxy hxz
  -- y is normal, so hyw : ReflTrans R y w must be refl
  have hy_eq : y = w := by
    rcases hyw.cases_head with heq | ⟨b, hstep, _⟩
    · exact heq
    · exfalso; exact hy _ hstep
  have hz_eq : z = w := by
    rcases hzw.cases_head with heq | ⟨b, hstep, _⟩
    · exact heq
    · exfalso; exact hz _ hstep
  rw [hy_eq, hz_eq]

/-! ## Direction 2: unique normal form ⟹ Confluence
    
  Technically, "unique normal form per orbit" is WEAKER than confluence
  in general (because it doesn't handle non-normalizing cases). Under
  assumption of termination (every reduction reaches a normal form),
  the two are equivalent. -/

/-- Strong normalization: every reduction sequence from x terminates. -/
def StronglyNormalizing (R : α → α → Prop) (x : α) : Prop :=
  ∃ y, Relation.ReflTransGen R x y ∧ IsNormal R y

/-- Unique-normal-form property: every state has at most one normal form. -/
def HasUniqueNormals (R : α → α → Prop) : Prop :=
  ∀ x y z, Relation.ReflTransGen R x y →
           Relation.ReflTransGen R x z →
           IsNormal R y → IsNormal R z → y = z

/-- Confluence implies unique-normals. -/
theorem confluent_implies_unique_normals {R : α → α → Prop}
    (hc : IsConfluent R) : HasUniqueNormals R :=
  confluent_implies_unique_normal hc

/-! ## Main equivalence (partial, under termination) -/

/-- For TERMINATING systems (every state reaches a normal form),
    confluence ⟺ uniqueness of normal forms.

    This is a specialization of Church-Rosser for normalizing
    rewriting. Full equivalence without termination requires
    more machinery (co-induction / infinite reductions). -/
theorem confluence_iff_unique_normals_when_terminating
    {R : α → α → Prop}
    (hSN : ∀ x, StronglyNormalizing R x) :
    IsConfluent R ↔ HasUniqueNormals R := by
  constructor
  · exact confluent_implies_unique_normals
  · intro hUN x y z hxy hxz
    obtain ⟨ny, hyn, hny⟩ := hSN y
    obtain ⟨nz, hzn, hnz⟩ := hSN z
    have hyn_full : Relation.ReflTransGen R x ny :=
      Relation.ReflTransGen.trans hxy hyn
    have hzn_full : Relation.ReflTransGen R x nz :=
      Relation.ReflTransGen.trans hxz hzn
    have : ny = nz := hUN x ny nz hyn_full hzn_full hny hnz
    exact ⟨ny, hyn, this ▸ hzn⟩

/-! ## Claim 2' interpretation -/

/-- CLAIM 2' (formalized): For a refinement system R that terminates
    (reaches normal forms), scale-invariance of the limit is
    equivalent to confluence.
    
    "Normal form" = limit of refinement = scale-invariant state.
    "Unique normal form" = unique scale-invariant limit = scale-invariant
                           structure is determined.
    "Confluence" = refinement path-independence. -/
theorem claim2_equivalence {R : α → α → Prop}
    (hSN : ∀ x, StronglyNormalizing R x) :
    IsConfluent R ↔ HasUniqueNormals R :=
  confluence_iff_unique_normals_when_terminating hSN

/-- Applied to DRLT: γ-refinement on simplicial networks.
    Scale-invariant limit exists (assumed) and is UNIQUE iff
    γ is confluent. FND_032 Part A proved γ confluent (simplicial
    commutativity). Hence the limit is unique.
    
    In Lean we state the abstract principle; the concrete γ case
    belongs to simplicial geometry (not formalized here). -/
theorem drlt_limit_unique_via_confluence {R : α → α → Prop}
    (hSN : ∀ x, StronglyNormalizing R x)
    (hc : IsConfluent R) : HasUniqueNormals R :=
  (claim2_equivalence hSN).mp hc

end DRLT.Foundation.Claim2
