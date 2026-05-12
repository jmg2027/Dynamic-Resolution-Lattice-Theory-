import E213.Lib.Math.CayleyDickson.CDDouble
import E213.Lib.Math.CayleyDickson.CDTower
import E213.Lib.Math.CayleyDickson.Cayley
import E213.Lib.Math.CayleyDickson.CayleyHeavy
import E213.Lib.Math.CayleyDickson.F2CDTower
import E213.Lib.Math.CayleyDickson.LipschitzHeavy
import E213.Lib.Math.CayleyDickson.LipschitzLens
import E213.Lib.Math.CayleyDickson.Pathion
import E213.Lib.Math.CayleyDickson.PathionHeavy
import E213.Lib.Math.CayleyDickson.R5Vacuity
import E213.Lib.Math.CayleyDickson.Sedenion
import E213.Lib.Math.CayleyDickson.SedenionHeavy
import E213.Lib.Math.CayleyDickson.Trigintaduonion
import E213.Lib.Math.CayleyDickson.TrigintaduoionionHeavy
import E213.Lib.Math.CayleyDickson.Z2Instance
import E213.Lib.Math.CayleyDickson.ZI
import E213.Lib.Math.CayleyDickson.ZIArith
import E213.Lib.Math.CayleyDickson.ZIDomain
import E213.Lib.Math.CayleyDickson.ZIHom
import E213.Lib.Math.CayleyDickson.ZIInstance
import E213.Lib.Math.CayleyDickson.ZOmega
import E213.Lib.Math.CayleyDickson.ZOmegaDomain
import E213.Lib.Math.CayleyDickson.ZOmegaInstance
import E213.Lib.Math.CayleyDickson.ZSqrt
import E213.Lib.Math.CayleyDickson.ZSqrt2
import E213.Lib.Math.CayleyDickson.ZSqrt2Domain
import E213.Lib.Math.CayleyDickson.ZSqrtDomain
import E213.Lib.Math.CayleyDickson.ZSqrtInstance
import E213.Lib.Math.CayleyDickson.ZSqrtProduct

/-! Spec-as-code entry point for `E213.Lib.Math.CayleyDickson`.

  Cayley–Dickson layered construction over 213.  Each layer is a
  CD doubling of the previous, producing the classical algebra
  tower at integer coefficients (no Mathlib, no `ring`, no
  Classical).

  ## Codomain witnesses (counterexamples to "R1–R4 force ℂ")

    * `ZI`        — Gaussian integers `ℤ[i]`           (D = 1)
    * `ZSqrt2`    — `ℤ[√-2]` and the parametric        (D = 2)
    * `ZOmega`    — Eisenstein integers `ℤ[ω]`         (cross-term norm)
    * `ZSqrt D`   — parametric family for any D > 0    (any positive D)

    Each is a `ConjugationCodomain` instance witnessing that the
    three-tier codomain spec (`CommBinaryCodomain` + `NonVanishing`
    + `Conjugation`, formerly the "R1–R4" axiom set in the
    deprecated R1–R5 frame) does NOT pin the codomain to ℂ.

  ## CD tower (structural drop ladder)

    * `CDDouble`     — CD doubling of ZI → Lipschitz quaternions.
                       R2 (commutativity) drops here.
    * `Cayley`       — CD doubling of Lipschitz → integer octonions.
                       Associativity drops here.
    * `Sedenion`     — CD doubling of Cayley → integer sedenions.
                       R3 (no zero divisors) drops here.  Moreno's
                       (e_3 + e_10)·(e_6 - e_15) = 0 witness.
    * `Trigintaduonion` — Sedenion × Sedenion (32-dim).
    * `Pathion`      — Trigintaduonion × Trigintaduonion (64-dim).

  ## Domain proofs

    * `ZIDomain`,
      `ZOmegaDomain`,
      `ZSqrtDomain`,
      `ZSqrt2Domain`  — `normSq u · v = normSq u · normSq v` etc.
    * `ZIArith`,
      `ZIHom`         — extra ZI lemmas + ring-hom witness for `conj`.

  ## Tactic-derived instances

    * `ZIInstance`,
      `Z2Instance`,
      `ZOmegaInstance`,
      `ZSqrtInstance` — `derive_conjugation_codomain` /
      `quad_extension D` macro outputs.

  ## Status

  All 29 files included (post-2026-05-06 deferred-cluster repair).
  The 9 formerly-deferred files (CDTower, CayleyHeavy, LipschitzHeavy,
  LipschitzLens, PathionHeavy, R5Vacuity, SedenionHeavy,
  TrigintaduoionionHeavy, ZSqrtProduct) all build clean.  Method:
  fix `Lens` → `Lens` namespace drift (already done in
  the Lens-cluster A-task); update doubled-vs-single namespace
  paths in the `hurwitz_ring` macro (Pathion / Trigintaduonion /
  Sedenion / ZI use doubled `X.X.foo`, Cayley / CDDouble.Lipschitz
  use single); add missing `open` lines for the type names
  (`Lipschitz`, `Cayley`, etc.) in each Heavy file; route the
  `normSq` / `mul_assoc` / etc. references in CDTower from the
  no-longer-existing `Cayley.normSq` to `CayleyHeavy.normSq` and
  `LipschitzHeavy.{normSq_mul, mul_assoc, no_zero_div}`.  See
  `research-notes/HIERARCHICAL_PLACEMENT.md` §6.2.
-/
