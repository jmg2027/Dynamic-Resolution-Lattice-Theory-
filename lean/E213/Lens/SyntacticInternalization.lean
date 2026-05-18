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

end E213.Lens.SyntacticInternalization
