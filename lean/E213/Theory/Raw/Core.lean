import E213.Term.Tree

/-!
# Theory.Raw.Core: canonical-form subtype

`Raw` 의 public 표면.  Underlying `Tree` machinery (inductive +
`cmp` + `canonical`) 는 Term 링의 `Term/Internal/Tree.lean` 에
있음 — ARCHITECTURE.md (2026-05-12) "Raw 의 구현체 (Tree 등)"
spec 에 따른 분리.

이 파일은 그 Tree 위에 `Raw := {t : Tree // canonical t}` 를
얹는 layer — Theory ring 의 Raw axiom public 표면.
-/

namespace E213.Theory

open E213.Term.Internal

-- ═══ Public type: canonical-form Raw ═══

def Raw : Type := { t : Tree // t.canonical = true }

instance : DecidableEq Raw := fun ⟨x, _⟩ ⟨y, _⟩ =>
  match decEq x y with
  | .isTrue h  => .isTrue (Subtype.ext h)
  | .isFalse h => .isFalse (fun e => h (congrArg Subtype.val e))

protected def Raw.a : Raw := ⟨.a, rfl⟩
protected def Raw.b : Raw := ⟨.b, rfl⟩

end E213.Theory
