/-!
# Firmware.Raw.Core: canonical-form subtype

Foundational module — the ordered `Tree` scaffolding lives in
the sub-namespace `E213.Theory.Internal` so downstream code
that does `open E213.Theory` does NOT see it.  Sub-modules
within `Firmware/Raw/` open `E213.Theory.Internal` explicitly.

Split out of monolithic `Raw.lean` () for incremental
compilation.
-/

namespace E213.Theory.Internal

-- ═══ Internal scaffolding: ordered tree ═══

inductive Tree : Type
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree
  deriving DecidableEq, Repr

def Tree.cmp : Tree → Tree → Ordering
  | .a,         .a         => .eq
  | .a,         .b         => .lt
  | .a,         .slash _ _ => .lt
  | .b,         .a         => .gt
  | .b,         .b         => .eq
  | .b,         .slash _ _ => .lt
  | .slash _ _, .a         => .gt
  | .slash _ _, .b         => .gt
  | .slash x₁ y₁, .slash x₂ y₂ =>
      match Tree.cmp x₁ x₂ with
      | .eq => Tree.cmp y₁ y₂
      | .lt => .lt
      | .gt => .gt

def Tree.canonical : Tree → Bool
  | .a         => true
  | .b         => true
  | .slash x y =>
      x.canonical && y.canonical &&
      (match Tree.cmp x y with | .lt => true | _ => false)

end E213.Theory.Internal

namespace E213.Theory

open E213.Theory.Internal

-- ═══ Public type: canonical-form Raw ═══

def Raw : Type := { t : Tree // t.canonical = true }

instance : DecidableEq Raw := fun ⟨x, _⟩ ⟨y, _⟩ =>
  match decEq x y with
  | .isTrue h  => .isTrue (Subtype.ext h)
  | .isFalse h => .isFalse (fun e => h (congrArg Subtype.val e))

def Raw.a : Raw := ⟨.a, rfl⟩
def Raw.b : Raw := ⟨.b, rfl⟩

end E213.Theory
