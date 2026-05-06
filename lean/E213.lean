-- Layered entry point for 213.
-- Canonical ring-model architecture: lean/E213/ARCHITECTURE.md
--
-- Concentric rings (imports flow inward):
--
--   E213.Term     — type-theoretic primitives, 0-axiom mechanism
--   E213.Theory   — Raw axiom + forced-shape uniqueness
--   E213.Lens     — Lens catamorphism algebra
--   E213.Meta     — metatheory of the framework
--   E213.Lib.Math — mathematics library (495 files)
--   E213.Lib.Physics — physics library (128 files)
--   E213.App      — applications
--
-- The library rings (Lib.Math, Lib.Physics) have large dependency
-- closures and are *not* imported here en masse — consumers should
-- import the specific Lib.Math.<x> or Lib.Physics.<x> they need.

import E213.Term
import E213.Theory
import E213.Lens
import E213.Meta
import E213.App

-- Universal Math infrastructure used at this top level.
import E213.Lib.Math.Pigeonhole
