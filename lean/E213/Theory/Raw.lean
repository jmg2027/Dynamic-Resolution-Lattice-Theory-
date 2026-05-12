import E213.Theory.Raw.Core
import E213.Term.Internal.Tree.Cmp
import E213.Theory.Raw.Slash
import E213.Theory.Raw.Fold
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Levels
import E213.Theory.Raw.Signed
import E213.Theory.Raw.Hom
import E213.Theory.Raw.Rec

/-!
# Theory.Raw: public Raw API (re-export shim)

The Raw module is split into sub-modules under `Theory/Raw/`
for incremental compilation.  This file re-exports the public
surface; downstream code does `import E213.Theory.Raw` and gets
everything below.

**Public API (exports):**
- `Raw` (opaque to consumers)
- `Raw.a`, `Raw.b` — the two atomic somethings
- `Raw.slash : (x y : Raw) → x ≠ y → Raw` — the "distinction"
- `Raw.slash_comm` — symmetric: `x/y = y/x`
- `Raw.depth`, `Raw.leaves` — observables
- `Raw.fold` — catamorphism (with `fold_a`, `fold_b`, `fold_slash`)
- `Raw.swap` — automorphism (with `swap_a`, `swap_b`, `swap_swap`)
- `Raw.swap_depth`, `Raw.swap_leaves` — swap invariances
- `Raw.fold_eq_depth`, `Raw.fold_eq_leaves` — bridges
- `Raw.fold_signed_swap` — signed Lens = negation
- `Raw.fold_swap_hom` — general hom-swap
- `Raw.rec` — custom eliminator with `@[elab_as_elim]`

**Forbidden to consumers:** the internal `Tree` scaffolding is
in `E213.Theory.Internal` — out of the way of `open
E213.Theory`.  Downstream code uses only the `Raw.*` API.

**Not re-exported here** (import the sub-module directly when
needed): `Raw.swap_slash` (compatibility theorem; see
`Theory/Raw/SwapSlash.lean`, used by `Lens/Instances/Swap.lean`).
-/
