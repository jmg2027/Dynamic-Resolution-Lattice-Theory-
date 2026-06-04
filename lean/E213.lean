-- Layered entry point for 213.
-- Canonical layer architecture: lean/E213/ARCHITECTURE.md (2026-05-12).
--
-- 4 ring + Meta (each ring uses immediate-below ring's API + Meta):
--
--   E213.Term     — Raw 의 구현체 (Tree 등)
--   E213.Theory   — Term API 위 Raw axiom + forced-shape uniqueness
--   E213.Lens     — Theory API 위 Lens catamorphism algebra
--   E213.Lib.Math, E213.Lib.Physics — Lens API 위 content libraries
--   E213.Meta     — ring-independent (Lean 4 bridge); usable from any ring
--
-- The library rings (Lib.Math, Lib.Physics) have large dependency
-- closures and are *not* imported here en masse — consumers should
-- import the specific Lib.Math.<x> or Lib.Physics.<x> they need.

import E213.Term
import E213.Theory
import E213.Lens
import E213.Meta

-- Universal Math infrastructure used at this top level.
import E213.Lib.Math.Combinatorics.Pigeonhole

-- App/ legacy tier removed 2026-05-13 Session H — its sole member
-- (App/Simplex.lean) moved to `Lib/Math/Combinatorics/Simplex5.lean`
-- since its content (block-pair classification on Fin 5, S_3 × S_2
-- invariance) is math combinatorics, not user-facing executable.
