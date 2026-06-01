import E213.Term.Tree
import E213.Theory.Raw.Slash

/-!
# Theory.Raw.Fold: Raw-level catamorphism + slash compatibility

Tree-level `fold` (def + recursion) lives in
`Term/Internal/Tree/Fold.lean`.  This file lifts it to `Raw` and
proves `fold_slash` — the homomorphism interaction with the
canonical smart constructor under symmetric `combine`.

**WARNING — axiom compliance (AXIOM.md §3)**: see Tree.fold note;
asymmetric `combine` makes the Lens silently leak the canonical
choice.  Every use of `Raw.fold` must verify symmetry.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

/-- Catamorphism on Raw. -/
protected def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl

protected theorem Raw.fold_a {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.a = ba := rfl

protected theorem Raw.fold_b {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.b = bb := rfl

/-- Fold / slash compatibility for symmetric `combine`. -/
protected theorem Raw.fold_slash {α : Type}
    (ba bb : α) (c : α → α → α)
    (hsym : ∀ u v : α, c u v = c v u)
    (x y : Raw) (h : x ≠ y) :
    Raw.fold ba bb c (Raw.slash x y h)
      = c (Raw.fold ba bb c x) (Raw.fold ba bb c y) := by
  unfold Raw.slash Raw.fold
  split <;> rename_i hc
  · show c (Tree.fold ba bb c x.val) (Tree.fold ba bb c y.val)
         = c (Tree.fold ba bb c x.val) (Tree.fold ba bb c y.val)
    rfl
  · show c (Tree.fold ba bb c y.val) (Tree.fold ba bb c x.val)
         = c (Tree.fold ba bb c x.val) (Tree.fold ba bb c y.val)
    exact hsym _ _
  · exact absurd (Tree.cmp_eq_to_eq _ _ hc) (fun e => h (Subtype.ext e))

/-- **Reading-equivalence (`↔`) fold/slash homomorphism** for `Prop`-valued
    readings — the 213-native form of `fold_slash`.

    `Raw.fold_slash` states slash-coherence as a function `=` (`c u v = c v u`),
    which for a `Prop`/function-valued codomain pulls `funext` (= `Quot.sound`)
    and `propext`.  But the residue's directionless slash (`a/b = b/a`,
    `seed/AXIOM/03_form.md` §3.4) only ever needs the readings to *distinguish
    the same things* — a **pointwise `↔`**, not Lean `=`.  Stated that way the
    homomorphism is **∅-axiom**: the canonicalisation swap (`cmp = gt`) is
    absorbed by the pointwise symmetry `hsym`, with no `funext`/`propext`.

    This is the PURE primitive for stating the `Prop`-valued Lens
    `combine_sym` / `view_eq` family as Reading-equivalences rather than
    function-`=`. -/
protected theorem Raw.fold_slash_iff
    (ba bb : Raw → Prop) (c : (Raw → Prop) → (Raw → Prop) → (Raw → Prop))
    (hsym : ∀ u v s, c u v s ↔ c v u s)
    (x y : Raw) (h : x ≠ y) (s : Raw) :
    Raw.fold ba bb c (Raw.slash x y h) s
      ↔ c (Raw.fold ba bb c x) (Raw.fold ba bb c y) s := by
  unfold Raw.slash Raw.fold
  split <;> rename_i hc
  · exact Iff.rfl
  · exact hsym _ _ s
  · exact absurd (Tree.cmp_eq_to_eq _ _ hc) (fun e => h (Subtype.ext e))

/-- **Relation-valued fold/slash homomorphism** — the codomain-polymorphic
    form of `fold_slash` / `fold_slash_iff`.  For *any* reflexive relation `R`
    on `α` under which `combine` is symmetric (`R (c u v) (c v u)`), folding
    over `Raw.slash x y h` is `R`-related to `c (fold x) (fold y)`.  The
    canonical-form swap (`cmp = gt`) is absorbed by `hsym`; the equal branch by
    reflexivity.  ∅-axiom — no `funext`/`propext` (the `=`-form needs `hsym` as a
    function-`=`, which at a function/`Prop` codomain pulls those).  Specialises
    to `fold_slash` (`R := Eq`) and `fold_slash_iff` (`R := pointwise ↔`). -/
protected theorem Raw.fold_slash_rel {α : Type} (R : α → α → Prop)
    (Rrefl : ∀ a, R a a) (ba bb : α) (c : α → α → α)
    (hsym : ∀ u v, R (c u v) (c v u))
    (x y : Raw) (h : x ≠ y) :
    R (Raw.fold ba bb c (Raw.slash x y h))
      (c (Raw.fold ba bb c x) (Raw.fold ba bb c y)) := by
  unfold Raw.slash Raw.fold
  split <;> rename_i hc
  · exact Rrefl _
  · exact hsym _ _
  · exact absurd (Tree.cmp_eq_to_eq _ _ hc) (fun e => h (Subtype.ext e))

end E213.Theory
