import E213.Lib.Math
import E213.Lib.Physics

/-! Spec-as-code entry point for `E213.Lib`.

  Library ring of the 213 architecture — content built using the
  framework rings (Term / Theory / Lens / Meta), as opposed to the
  framework itself.

  ## Sub-libraries

    * `Math/`     — 213-native mathematics (Cohomology / DyadicFSM /
                    HodgeConjecture / Real213 / Analysis / CayleyDickson
                    / Cauchy / and many other topical sub-trees)
    * `Physics/`  — 213-native physics (AlphaEM / Couplings / Mass /
                    Hadron / Higgs / Mixing / Cosmology / Foundations /
                    Substrate / Capstones / and other observable
                    domains)

  Each Lib sub-tree is its own bounded context with explicit
  `Bridge.lean` files for cross-context citations.

  Per `ARCHITECTURE.md` ring model, Lib content sits between Meta
  (metatheory) and App (applications) — Lib uses the framework
  to derive content; App uses Lib + framework to produce
  user-facing results.
-/
