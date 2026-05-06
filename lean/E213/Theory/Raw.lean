import E213.Theory.Raw.Core
import E213.Theory.Raw.Cmp
import E213.Theory.Raw.Slash
import E213.Theory.Raw.Fold
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Levels
import E213.Theory.Raw.Signed
import E213.Theory.Raw.Hom
import E213.Theory.Raw.Rec

/-!
# Firmware: Raw API (re-export shim)

refactor: the monolithic `Raw.lean` has been split
into sub-modules under `Firmware/Raw/` for incremental
compilation.  This file is a pure re-export for backwards
compatibility — downstream code can still `import
E213.Theory.Raw` and get the full public API.

**Public API (exports):**
- `Raw` (opaque to consumers)
- `Raw.a`, `Raw.b` — the two base somethings
- `Raw.slash : (x y : Raw) → x ≠ y → Raw` — the "distinction"
- `Raw.slash_comm` — symmetric: `x/y = y/x`
- `Raw.depth`, `Raw.leaves` — observables
- `Raw.fold` — catamorphism (with `fold_a`, `fold_b`, `fold_slash`)
- `Raw.swap` — automorphism (with `swap_a`, `swap_b`, `swap_swap`)
- `Raw.swap_depth`, `Raw.swap_leaves` — swap invariances
- `Raw.fold_eq_depth`, `Raw.fold_eq_leaves` — bridges
- `Raw.fold_signed_swap` — signed Lens = negation
- `Raw.fold_swap_hom` — general hom-swap
- `Raw.rec` — custom eliminator (3)

**Forbidden to consumers:** the internal `Tree` scaffolding is
in `E213.Theory.Internal` — out of the way of `open
E213.Theory`.  Downstream code uses only the `Raw.*` API.
-/
