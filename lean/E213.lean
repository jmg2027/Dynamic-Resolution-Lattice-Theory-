-- Layered entry point for 213.
-- Canonical theoretical layer architecture: lean/E213/ARCHITECTURE.md
--
-- Per the Stage M11 organization sweep, every top-level layer now has
-- its own umbrella file:
--
--   * E213.Kernel       — bare-metal type-theory primitives + tactics
--   * E213.Firmware     — Raw monad + forced-shape uniqueness scaffold
--   * E213.Hypervisor   — Lens algebra (instances, lattice, kernel, …)
--   * E213.Meta         — reflective primitives + meta tactics
--   * E213.App          — application-tier executables
--   * E213.Math         — math-cluster topical umbrella
--   * E213.Physics      — physics-cluster topical umbrella
--
-- (Pre-M14: an `E213.OS` umbrella also existed; it was dissolved in
-- Phase A — HodgeConjecture motivic bridges absorbed into
-- Math.Cohomology.HodgeConjecture.MotivicBridge, physics capstones
-- absorbed into Physics.Capstones.)
--
-- The Math and Physics topical umbrellas have large dependency
-- closures and are *not* imported here en masse — consumers should
-- import the specific Math.<x> or Physics.<x> they need.

import E213.Kernel
import E213.Firmware
import E213.Hypervisor
import E213.Meta
import E213.App

-- Universal Math infrastructure used at this top level.
import E213.Math.Pigeonhole
