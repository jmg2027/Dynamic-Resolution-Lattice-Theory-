import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.Common
import E213.Lib.Math.Algebra.GRA.NumberTheory
import E213.Lib.Math.Algebra.GRA.Graph
import E213.Lib.Math.Algebra.GRA.Analysis
import E213.Lib.Math.Algebra.GRA.Cohomology
import E213.Lib.Math.Algebra.GRA.HoTT
import E213.Lib.Math.Algebra.GRA.HigherAlgebra
import E213.Lib.Math.Algebra.GRA.Translation
import E213.Lib.Math.Algebra.GRA.Category
import E213.Lib.Math.Algebra.GRA.Groupoid
import E213.Lib.Math.Algebra.GRA.Hom
import E213.Lib.Math.Algebra.GRA.DepthFunctor
import E213.Lib.Math.Algebra.GRA.Enrichment
import E213.Lib.Math.Algebra.GRA.Naturality
import E213.Lib.Math.Algebra.GRA.SectionRetraction
import E213.Lib.Math.Algebra.GRA.Monoidal
import E213.Lib.Math.Algebra.GRA.LensBridge
import E213.Lib.Math.Algebra.GRA.CarrierRealization
import E213.Lib.Math.Algebra.GRA.Universality23
import E213.Lib.Math.Algebra.GRA.HasDistinguishing213
import E213.Lib.Math.Algebra.GRA.LensIsoCapstone

/-! # GRA (Graded Residue Arithmetic) — umbrella

Marathon 16 (closed): the universal (2,3)-graded meta-structure of 213.

  ## Phases 1–6 — Universality + Translation

  * `GRAModel`        — 7-axiom typeclass + `GRAIso` refl/symm/trans
  * `Common`          — shared PURE Nat arithmetic (coprime, reach,
                        depth formula, depth comparison)
  * `NumberTheory`    — hub instance on ℕ
  * `Graph`           — R₄ walk-length reading + iso to NT
  * `Analysis`        — R₅ resolution-exponent reading + iso to NT
  * `Cohomology`      — R₁ cochain-degree reading + iso to NT
  * `HoTT`            — R₃ truncation-level reading + iso to NT
  * `HigherAlgebra`   — R₂ operad-level reading + iso + universality capstone
  * `Translation`     — 5-way master translation + universal depth prediction

  ## Phases 7–11 — Category theory

  * `Category`        — 213-native `Cat`-typeclass, `GRACat`,
                        `ReadingCat` (6 closed (2,3)-models +
                        connectedness witness)
  * `Groupoid`        — every `GRAIso` is invertible; connected
                        groupoid structure on `ReadingCat`;
                        `Reading.hubAtNT` witnesses hub-and-spoke
  * `Hom`             — `GRAHom` (more general than iso),
                        category laws, forgetful `GRAIso → GRAHom`
  * `DepthFunctor`    — `(2,3)`-depth is a **constant functor** on
                        `ReadingCat`; `Reading_depth_const` proves
                        all 6 Readings agree on `⌈n/3⌉`
  * `Enrichment`      — unified bipartite-constrained carrier
                        for all five Readings.  `BipartiteCarrier`
                        is a `Nat` tagged with the (2, 3)-
                        bipartite constraint `n = 0 ∨ n ≥ 2`.
                        `GRA23_Bipartite` is the enriched GRA
                        model; `forgetHom : BipartiteCarrier →
                        Nat` is the canonical projection to NT.
                        Carries identical content for what the
                        five domain Readings (Walk / Cochain /
                        Truncation / Operad / Resolution)
                        encode — the domain flavour was
                        commentary, not structure.

  ## Phases 12–15 — Naturality + retraction + monoidal

  * `Naturality`                  — translation between the enriched
                                    bipartite carrier and `NT` is natural
                                    with respect to the forgetful;
                                    `DepthNaturality` captures the
                                    depth-preservation statement
  * `SectionRetraction`           — the forgetful has a section on its
                                    valid image (`n = 0 ∨ n ≥ 2`);
                                    `BipartiteRetract` structures up the
                                    data
  * `Monoidal`                    — `product : GRAModel → GRAModel →
                                    GRAModel`, the (2, 3)-monoidal product;
                                    `trivial23` as the unit; `leftUnitHom`
                                    and `rightUnitHom` as the unit isos

  ## Phase 16 — Lens bridge (Cat / HoTT as Readings)

  * `LensBridge`                  — `Raw.fold 2 3 (· + ·)` as the
                                    canonical Raw → Nat grade map;
                                    `bipartiteGradeMap` is definitionally
                                    equal to it.  All five domain
                                    Readings (Walk / Cochain / Truncation
                                    / Operad / Resolution) factor through
                                    `BipartiteCarrier.n` to the same Raw-
                                    level kernel.

  ## Phase 17 — Carrier realization (closes the Phase 16 open frontier)

  * `CarrierRealization`          — `canonical_ge_2 : ∀ r,
                                    canonicalGradeMap r ≥ 2` enables
                                    direct construction of
                                    `bipartiteRealize : Raw →
                                    BipartiteCarrier`, bypassing
                                    `Raw.fold_slash`'s `combine_sym`
                                    requirement.  The realization's
                                    grade projection equals
                                    `canonicalGradeMap` by `rfl`.

  ## Phase 18 — Universal property (1-cat proxy for GRACat-as-Cat)

  * `Universality23`              — `canonicalGradeMap_universal`:
                                    any function `f : Raw → Nat` with
                                    `f Raw.a = 2`, `f Raw.b = 3`, and
                                    slash-additive (`f (slash x y h) =
                                    f x + f y`) equals
                                    `canonicalGradeMap` pointwise.
                                    `canonical_arithmetic_forced`
                                    capstones the parameterless
                                    forcing statement.

  ## Phases 19–21 — HasDistinguishing213 (unified universe-polymorphic typeclass)

  * `HasDistinguishing213`        — single universe-polymorphic
                                    distinguishing structure
                                    `HasDistinguishing213.{u, v} α`,
                                    consolidating Phases 19–21's three
                                    exploratory variants
                                    (`HasDistinguishingU`,
                                    `HasDistinguishingW`,
                                    `HasDistinguishingWFull`).  Fields:
                                    `a, b : α`, `combine : α → α → α`,
                                    `Equiv : α → α → Sort v` (with
                                    refl/symm/trans), `combine_sym`
                                    (up to `Equiv`), and
                                    `distinct_equiv : Equiv a b → False`.
                                    Setting `Equiv := Eq` recovers the
                                    strict form; setting
                                    `Equiv := GRAIso` recovers the
                                    categorical form.  Two instances:
                                    `liftedReadingHasDistinguishing213 :
                                    HasDistinguishing213.{1, 0}
                                    (ULift.{1, 0} Reading)` (strict
                                    case, `Equiv := Eq`) and
                                    `gra23HasDistinguishing213 :
                                    HasDistinguishing213.{1, 1} GRA23`
                                    (categorical case,
                                    `Equiv := GRAIso`).
                                    `productSwapIso` is the swap-iso
                                    witness of monoidal-product
                                    iso-commutativity;
                                    `trivial23_not_iso_NT` is the
                                    cardinality-based categorical
                                    distinctness lemma.

  ## Phase 22 — Lens.Unified × GRA capstone

  * `LensIsoCapstone`             — defines `gradeLens : Lens Nat` with
                                    `(2, 3, (· + ·))`, whose view IS
                                    `canonicalGradeMap` by `rfl`.  Phase
                                    18's universal property re-expressed
                                    in Lens vocabulary
                                    (`profile_view_eq_canonical`); from
                                    there `profile_lens_LensIso_gradeLens`
                                    proves every (2, 3)-profile Lens on
                                    Nat is `Lens.Unified.LensIso` to
                                    `gradeLens`.  The five Reading
                                    Lenses (`walkLens` ... `resolutionLens`)
                                    are explicit members; the five Phase
                                    17 realizations project to
                                    `gradeLens.view` by `rfl`.  The
                                    master capstone
                                    `gra_lens_iso_class_capstone` packages
                                    the universal property + 5 Reading
                                    `LensIso`s in one bundle.

Narrative: `theory/math/gra_book.md`,
`theory/essays/gra_as_substrate_of_cat_hott.md`.
**Strict ∅-axiom: all PURE / 0 DIRTY** (118 from Phases 1–6 + 49
from Phases 7–11 + ≈20 from Phases 12–15 unified Enrichment +
Naturality + SectionRetraction + Monoidal + ≈11 from Phase 16
Lens bridge + 7 from Phase 17 carrier realization + 13 from
Phase 18 universal property + 23 from Phases 19–21 unified
HasDistinguishing213 + 23 from Phase 22).  `ax_coprime` uses `gcd213`
(PURE) rather than Lean-core `Nat.gcd`.  Every proof uses kernel-decide,
`rfl`, or explicit Nat / `Meta.Nat.NatDiv213` / `Meta.Nat.AddMod213`
lemmas — no `omega`, no `simp`-driven rewrites, no Mathlib, no `Classical`.
-/
