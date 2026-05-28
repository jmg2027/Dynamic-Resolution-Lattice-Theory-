import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Graph
import E213.Lib.Math.GRA.Analysis
import E213.Lib.Math.GRA.Cohomology
import E213.Lib.Math.GRA.HoTT
import E213.Lib.Math.GRA.HigherAlgebra
import E213.Lib.Math.GRA.Translation

/-! # GRA (Graded Residue Arithmetic) — umbrella

Marathon 16 (closed): the universal (2,3)-graded meta-structure of 213.

  * `GRAModel`        — 7-axiom typeclass + `GRAIso` refl/symm/trans
  * `NumberTheory`    — hub instance on ℕ
  * `Graph`           — R₄ walk-length reading + iso to NT
  * `Analysis`        — R₅ resolution-exponent reading + iso to NT
  * `Cohomology`      — R₁ cochain-degree reading + iso to NT
  * `HoTT`            — R₃ truncation-level reading + iso to NT
  * `HigherAlgebra`   — R₂ operad-level reading + iso + universality capstone
  * `Translation`     — 5-way master translation + universal depth prediction

Narrative: `theory/math/gra_book.md`, `theory/math/graded_residue_arithmetic.md`.
Purity: 0 sorry, 0 Classical, 0 Mathlib, kernel-decide only.  Carries
`propext`/`Quot.sound` from omega — Tier 5.1 propext-unsealing backlog
per `STRICT_ZERO_AXIOM.md`.
-/
