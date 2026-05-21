import E213.Term.Tree

/-!
# Theory.Raw.Core: canonical-form subtype

The public surface of `Raw`.  The underlying `Tree` machinery
(inductive + `cmp` + `canonical`) lives in the Term ring at
`Term/Internal/Tree.lean` — separated per ARCHITECTURE.md.

This file exposes `Raw := {t : Tree // canonical t}` as the
Theory ring's public surface for the Raw axiom, built from the
underlying Tree.  The canonical-form subtype is the quotient
emulation (encoding cost §8a.1 — Lean 4 has no primitive
quotient; Tree.cmp selects one representative per slash-symmetry
equivalence class).  Tree.cmp's specific order is arbitrary;
cmp-independence is mechanically verified at
`Theory/RawCmpIndependence.lean`.
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
