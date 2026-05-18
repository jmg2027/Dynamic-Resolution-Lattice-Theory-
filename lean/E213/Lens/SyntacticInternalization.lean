import E213.Theory.Raw.API
import E213.Lens.Number.Nat213.Raw

/-!
# Lens.SyntacticInternalization — meta-syntax glyphs as Raws (§9.4 L2 prototype)

Per `seed/AXIOM/09_chart_relativity.md` §9.4 and
`research-notes/2026-05-18_lens_emergence_path.md` §2.7.  The
source-text glyphs we use to write 213 expressions —
`a`, `b`, `/`, `(`, `)`, `,`, whitespace — are themselves objects
that can be pointed at, hence Raws.

This file realises that observation concretely: we pick a 7-glyph
alphabet covering the basic source-text symbols and exhibit a
specific Raw for each glyph.  The mapping is injective: distinct
meta-syntactic glyphs land on distinct Raws.  The
meta-meta-… language cascade therefore *halts* at the first
encoding: writing the encoding requires only the same 7 glyphs,
themselves Raw-encoded.

## What this realises (and doesn't)

**Realises (positive):**
- Source-text glyphs have a Raw-internal home.  Anything we'd write
  in this Lean file (parentheses, commas, slashes) corresponds to a
  specific Raw via `Glyph.toRaw`.
- Injectivity means the encoding doesn't collapse the meta-alphabet.

**Out of scope (for this minimal L2 prototype):**
- No parser is defined.  Mapping a *list of glyphs* to the Raw it
  denotes (parsing) is non-trivial because of canonical-form
  reordering in `Raw.slash` and the `≠` precondition.  A full L3
  parser/printer round-trip is a future project.
- The user-facing source-text parens `(`, `)` correspond to tree
  shape (grouping) at the semantic level; that semantic
  correspondence is realised by the `Raw.slash` nesting itself,
  not by this glyph encoding.  This file is about the
  *glyph-symbol-as-Raw* layer.

∅-axiom standard; uses `decide` (kernel evaluation).
-/

namespace E213.Lens.SyntacticInternalization

open E213.Theory

/-! ### The 7-glyph alphabet -/

/-- The minimum meta-syntactic alphabet used in this codebase to
    write 213 expressions: atoms `a`, `b`; the slash referent `/`;
    parenthesis glyphs `(`, `)`; the comma separator `,`; and
    whitespace.  These are *source-text* symbols — what
    `seed/AXIOM/09_chart_relativity.md` §9.4 calls "glyphs". -/
inductive Glyph
  | a       -- atom symbol
  | b       -- atom symbol
  | slash   -- the `/` referent
  | lparen  -- `(`
  | rparen  -- `)`
  | comma   -- `,`
  | space   -- whitespace
  deriving DecidableEq, Repr

/-! ### Glyph → Raw encoding

We use the Method A chain to pick 7 distinct Raws (the 7 first
numerals).  Any 7-distinct-Raw choice would do; Method A is the
canonical one. -/

/-- Encode a glyph as a specific Raw.  Uses
    `Lens.Number.Nat213.Raw.numeral n` for `n = 0, ..., 6`.  -/
def Glyph.toRaw : Glyph → Raw
  | .a       => E213.Lens.Number.Nat213.Raw.numeral 0
  | .b       => E213.Lens.Number.Nat213.Raw.numeral 1
  | .slash   => E213.Lens.Number.Nat213.Raw.numeral 2
  | .lparen  => E213.Lens.Number.Nat213.Raw.numeral 3
  | .rparen  => E213.Lens.Number.Nat213.Raw.numeral 4
  | .comma   => E213.Lens.Number.Nat213.Raw.numeral 5
  | .space   => E213.Lens.Number.Nat213.Raw.numeral 6

/-! ### Injectivity — different glyphs land on different Raws -/

/-- The 7 designated Raws (the first 7 Method A numerals) are
    pairwise distinct.  Decidable by kernel evaluation. -/
theorem Glyph.toRaw_injective {g₁ g₂ : Glyph}
    (h : g₁.toRaw = g₂.toRaw) : g₁ = g₂ := by
  cases g₁ <;> cases g₂ <;>
    first | rfl | (exfalso; revert h; decide)

/-- Same statement in `Function.Injective`-friendly form. -/
theorem Glyph.toRaw_injective' :
    ∀ {g₁ g₂ : Glyph}, g₁.toRaw = g₂.toRaw → g₁ = g₂ :=
  @Glyph.toRaw_injective

/-! ### Cascade-halt witness

The `Glyph.toRaw` mapping is the entire meta-encoding needed.
Writing *this very file* uses only the 7 glyphs above plus their
arrangements; the arrangement (concatenation in source text) is
itself a list of glyphs.  At the L2 level, there is no need to
introduce L3 meta-meta-glyphs — the same 7-glyph alphabet
suffices to write about itself.  The cascade halts. -/

/-- Sentinel: there exists a Raw for every glyph.  Trivial
    statement included to make the "everything is Raw-encoded"
    claim explicit at the type level. -/
theorem Glyph.has_raw_image (g : Glyph) : ∃ r : Raw, r = g.toRaw :=
  ⟨g.toRaw, rfl⟩

/-! ### Polish-prefix printer (partial L3 — output side)

The printer converts a `Tree` (or `Raw`) into its Polish-prefix
glyph sequence.  Polish prefix needs no parentheses; the slash
glyph and the atom glyphs uniquely determine grouping by arity.

The full L3 round-trip (`parse ∘ print = id`) requires a parser
whose termination proof is non-trivial — left as future work.
This section provides the printer side and small sanity checks. -/

open E213.Term.Internal (Tree)

/-- Polish-prefix printer for `Tree`.  Each slash node prefixes
    its children's print outputs with the slash glyph. -/
def printTree : Tree → List Glyph
  | .a         => [.a]
  | .b         => [.b]
  | .slash x y => .slash :: printTree x ++ printTree y

theorem printTree_a : printTree .a = [.a] := rfl
theorem printTree_b : printTree .b = [.b] := rfl
theorem printTree_slash (x y : Tree) :
    printTree (.slash x y) = .slash :: printTree x ++ printTree y := rfl

/-- Printer lifted to `Raw` via the underlying canonical Tree. -/
def printRaw (r : Raw) : List Glyph := printTree r.val

theorem printRaw_a : printRaw Raw.a = [.a] := rfl
theorem printRaw_b : printRaw Raw.b = [.b] := rfl

/-- Concrete witness: `(a/b)` prints to the 3-glyph sequence
    `[slash, a, b]`. -/
example :
    printRaw (Raw.slash Raw.a Raw.b (by decide))
      = [.slash, .a, .b] := by decide

/-- Concrete witness: `(b/a)` is canonicalised to `(a/b)` and
    prints the same sequence — `Raw.slash_comm` is reflected in
    the printer. -/
example :
    printRaw (Raw.slash Raw.b Raw.a (by decide))
      = [.slash, .a, .b] := by decide

/-! ### L3 parser — fuel-bounded Polish prefix decoding

A constructive parser that consumes Polish-prefix glyphs from the
front of a list and returns the parsed Tree plus the leftover
glyphs.  Termination is by strict decrement of the fuel argument.

For any tree `t`, parsing `printTree t ++ rest` with sufficient
fuel returns `some (t, rest)`.  The round-trip theorem
(`parseTree_printTree`) is deferred — it would need a
fuel-monotonicity lemma plus a careful Nat arithmetic bound,
non-trivial to prove without `omega` (which carries `propext`).
The parser is provided constructively for use; concrete
round-trip checks via `decide` witness its correctness on small
trees. -/

/-- Polish-prefix parser, fuel-bounded.  Returns
    `(parsed tree, leftover glyphs)` on success, `none` on
    failure (out of fuel, unexpected glyph, or empty input). -/
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

/-- Top-level parser: consume one tree from the list, requiring no
    leftover.  Returns `some t` iff the entire input is exactly
    `printTree t`.  Fuel = list length (always sufficient). -/
def parseTree (gs : List Glyph) : Option Tree :=
  match parseHelper gs.length gs with
  | some (t, []) => some t
  | _ => none

/-- Concrete round-trip witness on `Raw.a` (1-glyph tree). -/
example : parseTree (printTree .a) = some .a := by decide

/-- Concrete round-trip witness on `Raw.b`. -/
example : parseTree (printTree .b) = some .b := by decide

/-- Concrete round-trip witness on `slash a b`. -/
example : parseTree (printTree (.slash .a .b)) = some (.slash .a .b) := by
  decide

/-- Concrete round-trip witness on a 3-leaf tree
    `slash b (slash a b)` (= `Raw.numeral 2`'s underlying Tree). -/
example :
    parseTree (printTree (.slash .b (.slash .a .b)))
      = some (.slash .b (.slash .a .b)) := by decide

end E213.Lens.SyntacticInternalization
