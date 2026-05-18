import E213.Term.Tree

/-!
# Theory.Raw.Core: canonical-form subtype

The public surface of `Raw`.  The underlying `Tree` machinery
(inductive + `cmp` + `canonical`) lives in the Term ring at
`Term/Internal/Tree.lean` — separated per the
ARCHITECTURE.md (2026-05-12) "Raw's implementation (Tree, etc.)"
spec.

This file layers `Raw := {t : Tree // canonical t}` on top of
that Tree — the Theory ring's public surface for the Raw axiom.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

-- ═══ Public type: canonical-form Raw ═══

def Raw : Type := { t : Tree // t.canonical = true }

instance : DecidableEq Raw := fun ⟨x, _⟩ ⟨y, _⟩ =>
  match decEq x y with
  | .isTrue h  => .isTrue (Subtype.ext h)
  | .isFalse h => .isFalse (fun e => h (congrArg Subtype.val e))

protected def Raw.a : Raw := ⟨.a, rfl⟩
protected def Raw.b : Raw := ⟨.b, rfl⟩

end E213.Theory
