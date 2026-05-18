import E213.Theory.Raw.API
import E213.Lens.Number.Nat213.Raw

/-!
# Lens.SyntacticInternalization — meta-syntax glyphs as Raws (§9.4 prototype)

Per `seed/AXIOM/09_chart_relativity.md` §9.4 and
`research-notes/2026-05-18_lens_emergence_path.md` §2.7.  The
source-text glyphs we use to write 213 expressions —
`a`, `b`, `/`, `(`, `)`, `,`, whitespace — are themselves objects
that can be pointed at, hence Raws.

This file realises that observation:
  - **L2**: 7-glyph alphabet, each glyph → a distinct Raw; the
    meta-meta-… cascade halts at L2.
  - **L3 (partial)**: Polish-prefix printer + fuel-bounded parser
    + concrete round-trip witnesses (`decide`-checked on small
    trees).  The universal round-trip theorem
    `∀ t, parseTree (printTree t) = some t` requires careful
    propext-free match-reduction handling and is documented at the
    bottom as future work.

∅-axiom standard; uses `decide` (kernel evaluation).
-/

namespace E213.Lens.SyntacticInternalization

open E213.Theory

/-! ### The 7-glyph alphabet -/

inductive Glyph
  | a
  | b
  | slash
  | lparen
  | rparen
  | comma
  | space
  deriving DecidableEq, Repr

/-! ### Glyph → Raw encoding -/

def Glyph.toRaw : Glyph → Raw
  | .a       => E213.Lens.Number.Nat213.Raw.numeral 0
  | .b       => E213.Lens.Number.Nat213.Raw.numeral 1
  | .slash   => E213.Lens.Number.Nat213.Raw.numeral 2
  | .lparen  => E213.Lens.Number.Nat213.Raw.numeral 3
  | .rparen  => E213.Lens.Number.Nat213.Raw.numeral 4
  | .comma   => E213.Lens.Number.Nat213.Raw.numeral 5
  | .space   => E213.Lens.Number.Nat213.Raw.numeral 6

theorem Glyph.toRaw_injective {g₁ g₂ : Glyph}
    (h : g₁.toRaw = g₂.toRaw) : g₁ = g₂ := by
  cases g₁ <;> cases g₂ <;>
    first | rfl | (exfalso; revert h; decide)

theorem Glyph.toRaw_injective' :
    ∀ {g₁ g₂ : Glyph}, g₁.toRaw = g₂.toRaw → g₁ = g₂ :=
  @Glyph.toRaw_injective

theorem Glyph.has_raw_image (g : Glyph) : ∃ r : Raw, r = g.toRaw :=
  ⟨g.toRaw, rfl⟩

/-! ### Polish-prefix printer -/

open E213.Term.Internal (Tree)

def printTree : Tree → List Glyph
  | .a         => [.a]
  | .b         => [.b]
  | .slash x y => .slash :: printTree x ++ printTree y

theorem printTree_a : printTree .a = [.a] := rfl
theorem printTree_b : printTree .b = [.b] := rfl
theorem printTree_slash (x y : Tree) :
    printTree (.slash x y) = .slash :: printTree x ++ printTree y := rfl

def printRaw (r : Raw) : List Glyph := printTree r.val

theorem printRaw_a : printRaw Raw.a = [.a] := rfl
theorem printRaw_b : printRaw Raw.b = [.b] := rfl

example :
    printRaw (Raw.slash Raw.a Raw.b (by decide))
      = [.slash, .a, .b] := by decide

example :
    printRaw (Raw.slash Raw.b Raw.a (by decide))
      = [.slash, .a, .b] := by decide

/-! ### Polish-prefix parser (fuel-bounded) -/

def parseHelper : Nat → List Glyph → Option (Tree × List Glyph)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .a :: rest => some (.a, rest)
  | _ + 1, .b :: rest => some (.b, rest)
  | n + 1, .slash :: rest =>
      match parseHelper n rest with
      | none => none
      | some (x, rest1) =>
          match parseHelper n rest1 with
          | none => none
          | some (y, rest2) => some (.slash x y, rest2)
  | _ + 1, _ :: _ => none

def parseTree (gs : List Glyph) : Option Tree :=
  match parseHelper gs.length gs with
  | some (t, []) => some t
  | _ => none

example : parseTree (printTree .a) = some .a := by decide
example : parseTree (printTree .b) = some .b := by decide
example : parseTree (printTree (.slash .a .b)) = some (.slash .a .b) := by
  decide
example :
    parseTree (printTree (.slash .b (.slash .a .b)))
      = some (.slash .b (.slash .a .b)) := by decide

/-! ### L3 universal round-trip — deferred work

The universal theorem `∀ t, parseTree (printTree t) = some t` is
provable in principle, with:
  - tree-size definition (`treeSize : Tree → Nat`),
  - fuel monotonicity (`parseHelper_fuel_mono`),
  - exact-size correctness (`parseHelper_printTree_append`),
  - length-vs-size inequality (`printTree_length_ge_size`).

The slash-induction step inside `parseHelper_fuel_succ` requires
careful match-reduction handling that, in Lean 4, can either pull
in `propext` (via simp's Iff lemmas) or require verbose explicit
`show ... rfl`-driven destructuring.  Both are doable; neither is
short.  The concrete-case `decide` witnesses above suffice for
day-to-day use until the universal proof is in. -/

end E213.Lens.SyntacticInternalization
