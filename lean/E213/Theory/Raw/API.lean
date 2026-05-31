import E213.Theory.Raw.Core
import E213.Term.Tree
import E213.Theory.Raw.Slash
import E213.Theory.Raw.Fold
import E213.Theory.Raw.Swap
import E213.Theory.Raw.SwapSlash
import E213.Theory.Raw.Levels
import E213.Theory.Raw.FoldSwap
import E213.Theory.Raw.Rec
import E213.Theory.Raw.Endomorphic
import E213.Theory.Raw.PrimitiveTower
import E213.Theory.Raw.Lambek
import E213.Theory.Raw.Congruence
import E213.Theory.Raw.ParenthesizationDistinct

/-!
# Theory.Raw.API — public surface (re-export shim)

Single import for external consumers of the Raw axiom.  Downstream
code (Lens, Lib, …) should write `import E213.Theory.Raw.API` and
get the full public surface in one line.

**Public API (exports)**:
- `Raw` (opaque to consumers)
- `Raw.a`, `Raw.b` — the two atomic somethings
- `Raw.slash : (x y : Raw) → x ≠ y → Raw` — the "distinction"
- `Raw.slash_comm` — symmetric: `x/y = y/x`
- `Raw.depth`, `Raw.leaves` — observables
- `Raw.fold` — catamorphism (with `fold_a`, `fold_b`, `fold_slash`)
- `Raw.swap` — automorphism (with `swap_a`, `swap_b`, `swap_swap`)
- `Raw.swap_slash` — swap ∘ slash compatibility
- `Raw.swap_depth`, `Raw.swap_leaves` — swap invariances
- `Raw.fold_eq_depth`, `Raw.fold_eq_leaves` — bridges
- `Raw.fold_signed_swap` — signed Lens = negation
- `Raw.fold_swap_hom` — general hom-swap
- `Raw.rec` — custom eliminator with `@[elab_as_elim]`
- `Theory.Raw.Endomorphic.{slashOrSelf, foldRaw, swapClosed}` —
  endomorphic catamorphism + total slash combinator (used by
  Lens.Number.Nat213 numbering-system isomorphism)
- `Theory.Raw.PrimitiveTower.{rawTower, rawTower_depth,
  primitive_tower_summary}` — the most primitive 213 tower: the
  single `slash` arrow iterated from the first distinguishing
  (`depth = level`, `depth < leaves` at every rung; ∅-axiom)

**Excluded from API** (intentional):
- `Theory.Raw.Demo` — bare-metal example chains for documentation
  only.  Not part of the API.

**Migration history**: an earlier `Theory.Raw.Mobius` (Möbius
matrix bridge) had a ring violation via `Lib.Math.Tactic.Ring213`;
it was promoted to `Lib/Math/Mobius213.lean` per `research-notes/archive/audits/THEORY_AUDIT.md`
§4 (now complete).  Möbius results are imported directly from
`Lib/Math/Mobius213` as Lib-ring content.

**Discipline** (per ARCHITECTURE.md): outside the Raw
sub-cluster (e.g., Lens, Lib, other Theory clusters), code should
import **only this `API.lean`**.  Direct reach-in to specific
sub-modules (`Theory.Raw.Slash`, `Theory.Raw.Fold`, …) is a
discipline violation — use this single entry point instead.

Tree machinery (the underlying `inductive Tree`, `Tree.cmp`,
`Tree.canonical`) lives in the Term ring at `Term/Internal/Tree*`.
This API includes `import E213.Term.Tree` so consumers of the Raw
axiom also receive the Tree surface needed for low-level proofs.
-/
