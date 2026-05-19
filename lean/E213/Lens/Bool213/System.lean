import E213.Theory.Raw.API
import E213.Lens.Bool213.Raw

/-!
# Lens.Bool213.System — meta pattern over (T, F) choices

Bool213, like Nat213, admits infinitely many realisations.  Any
pair of distinct Raws `T ≠ F` yields a valid Bool213 system.  This
file packages the meta-pattern and proves system-level isomorphism.

## Infinitely many Bool213 systems

  - methodA: T = Raw.a,        F = Raw.b
  - methodB: T = Raw.b,        F = Raw.a       (swap)
  - methodC: T = slash a b,    F = Raw.a       (slash + leaf)
  - methodD: T = Raw.a,        F = slash a b   (reverse)
  - ... infinitely many

Each `(T, F)` with `T ≠ F` gives a valid system.  Raw has
infinitely many canonical Trees, hence infinitely many systems.

## Isomorphism

The iso map between systems A and B is:
  iso A B : Raw → Raw
    r ↦ if r = A.T then B.T
        else if r = A.F then B.F
        else r  (fallback)

This preserves `not`, `and`, etc. (swap T↔F, table equivalence).
-/

namespace E213.Lens.Bool213.System

open E213.Theory

/-- 213-native Boolean system: `(T, F)` is a distinct Raw pair. -/
structure BooleanSystem where
  T : Raw
  F : Raw
  hTF : T ≠ F

/-- Negation in system S: T ↔ F swap; other inputs unchanged. -/
def not (S : BooleanSystem) (r : Raw) : Raw :=
  if r = S.T then S.F
  else if r = S.F then S.T
  else r

/-- Conjunction (`and`) in system S. Table-defined. -/
def and (S : BooleanSystem) (x y : Raw) : Raw :=
  if x = S.T ∧ y = S.T then S.T else S.F

/-! ### Method A: canonical (T = Raw.a, F = Raw.b) — the
Bool213.lean default -/

def methodA : BooleanSystem where
  T := Raw.a
  F := Raw.b
  hTF := by
    intro h
    have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
    exact Term.Internal.Tree.noConfusion hval

/-! ### Iso between systems -/

/-- A → B isomorphism.  T ↦ T', F ↦ F', otherwise fallback. -/
def iso (A B : BooleanSystem) (r : Raw) : Raw :=
  if r = A.T then B.T
  else if r = A.F then B.F
  else r

theorem iso_T (A B : BooleanSystem) : iso A B A.T = B.T := by
  unfold iso; rw [if_pos rfl]

theorem iso_F (A B : BooleanSystem) : iso A B A.F = B.F := by
  unfold iso
  rw [if_neg (Ne.symm A.hTF), if_pos rfl]

/-! ### Iso preserves operations -/

/-- The iso preserves `not`.  Aligns the T → F → T cycle across
    the two systems. -/
theorem iso_not (A B : BooleanSystem) (r : Raw) (hr : r = A.T ∨ r = A.F) :
    iso A B (not A r) = not B (iso A B r) := by
  rcases hr with hr | hr
  · -- r = A.T → not A r = A.F → iso = B.F.  RHS: iso r = B.T → not B B.T = B.F.
    subst hr
    show iso A B (not A A.T) = not B (iso A B A.T)
    rw [iso_T]
    show iso A B (not A A.T) = not B B.T
    unfold not
    rw [if_pos rfl, if_pos rfl]
    exact iso_F A B
  · -- r = A.F → not A r = A.T → iso = B.T.  RHS: iso r = B.F → not B B.F = B.T.
    subst hr
    show iso A B (not A A.F) = not B (iso A B A.F)
    rw [iso_F]
    show iso A B (not A A.F) = not B B.F
    unfold not
    rw [if_neg (Ne.symm A.hTF), if_pos rfl, if_neg (Ne.symm B.hTF), if_pos rfl]
    exact iso_T A B

/-- The iso preserves `and` (both arguments valid Bool in A). -/
theorem iso_and (A B : BooleanSystem) (x y : Raw)
    (hx : x = A.T ∨ x = A.F) (hy : y = A.T ∨ y = A.F) :
    iso A B (and A x y) = and B (iso A B x) (iso A B y) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy
  · -- (T, T): and = T → iso = B.T.  RHS: iso T = B.T, iso T = B.T, and B.T B.T = B.T.
    show iso A B (and A A.T A.T) = and B (iso A B A.T) (iso A B A.T)
    rw [iso_T]
    show iso A B (and A A.T A.T) = and B B.T B.T
    unfold and
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
    exact iso_T A B
  · -- (T, F): and = F → iso = B.F.  RHS: iso T = B.T, iso F = B.F, and B.T B.F = B.F.
    show iso A B (and A A.T A.F) = and B (iso A B A.T) (iso A B A.F)
    rw [iso_T, iso_F]
    unfold and
    rw [if_neg (fun ⟨_, h⟩ => A.hTF h.symm), if_neg (fun ⟨_, h⟩ => B.hTF h.symm)]
    exact iso_F A B
  · -- (F, T): and = F → iso = B.F.  RHS: iso F = B.F, iso T = B.T, and B.F B.T = B.F.
    show iso A B (and A A.F A.T) = and B (iso A B A.F) (iso A B A.T)
    rw [iso_T, iso_F]
    unfold and
    rw [if_neg (fun ⟨h, _⟩ => A.hTF h.symm), if_neg (fun ⟨h, _⟩ => B.hTF h.symm)]
    exact iso_F A B
  · -- (F, F): and = F → iso = B.F.  RHS: iso F = B.F, iso F = B.F, and B.F B.F = B.F.
    show iso A B (and A A.F A.F) = and B (iso A B A.F) (iso A B A.F)
    rw [iso_F]
    unfold and
    rw [if_neg (fun ⟨h, _⟩ => A.hTF h.symm), if_neg (fun ⟨h, _⟩ => B.hTF h.symm)]
    exact iso_F A B

end E213.Lens.Bool213.System
