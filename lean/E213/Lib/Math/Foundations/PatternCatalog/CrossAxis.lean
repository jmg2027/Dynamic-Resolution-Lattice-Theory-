import E213.Lib.Math.Foundations.PatternCatalog.Core
import E213.Lib.Math.Foundations.AxiomSystems.CrossTheoryCohabit

/-!
# PatternCatalog — Cross-Axis (Statement-Shape × Design-Pattern)

Reading the empirical audit corpus against this catalog
reveals that the audit's
**six functional families** classify theorems by *statement shape*,
while `PatternCatalog.lean`'s **six atomic games + 1 composite**
classify theorems by *codebase design pattern*.  These axes are
**orthogonal**.

## Concrete cross-cell evidence

 F2c cites verbatim the same theorem `cohabit_peano_depth`
that powers `peanoDepthCohabit : CohabitationWitness Raw Nat Nat` in
`PatternCatalogInstance.lean`.  That single theorem occupies cell
**F2 (bundled checks) × Cohabitation**.  No contradiction — the two
classifications see the same theorem from different angles.
-/

namespace E213.Lib.Math.Foundations.PatternCatalog.CrossAxis

open E213.Lib.Math.Foundations.PatternCatalog

/-- **Statement-shape axis** (audit corpus : the functional
    family of a theorem's *statement*. -/
inductive StatementShape where
  /-- F1 — atomic equality or inequality (≈ 52% of corpus). -/
  | atomicCheck
  /-- F2 — ∧-conjunction bundle (≈ 16%). -/
  | bundledChecks
  /-- F3 — universal `∀` dispatch (≈ 14%). -/
  | universal
  /-- F4 — implication chain `H → C` (≈ 10%). -/
  | implication
  /-- F5 — existential witness `∃` (≈ 4%). -/
  | existential
  /-- F6 — negative existence `¬ ∃` (≈ 3%). -/
  | negativeExist
  deriving DecidableEq, Repr

/-- **Design-pattern axis** (PatternCatalog: 4 atomic + 2 operator +
    composites, after H2 self-corrections). -/
inductive PatternGame where
  -- Atomic games (after Aggregation/ForcedUniq lifted to operators)
  | locality
  | typeclass
  | catamorphism
  | dynamical
  -- Operators (lift any game)
  | aggregateOp
  | forcedOp
  -- Atomic-pair composites (closure of binary products)
  | lens                  -- Typeclass × Cata
  | cohabitation          -- Lens × Lens (ternary)
  | localityInterface     -- Locality × Typeclass
  | localityCata          -- Locality × Cata
  | localityDynamical     -- Locality × Dynamical
  | interfaceDynamical    -- Typeclass × Dynamical (with coherence)
  | cataDynamical         -- Cata × Dynamical (with coherence)
  -- Operator-application composites
  | localityAggregate     -- Aggregate (LocalityWitness)
  | dynamicalAggregate    -- Aggregate (DynamicalWitness)
  | interfaceAggregate    -- Aggregate (InterfaceWitness)
  | cataAggregate         -- Aggregate (CatamorphismWitness)
  | localityForcedValue   -- Locality × Forced (per-index)
  | cataForcedForm        -- Cata × Forced (form-level)
  | dynamicalForcedPeriod -- Dynamical × Forced (period uniqueness)
  deriving DecidableEq, Repr

/-- One cross-axis cell: a (shape, game) pair. -/
structure CrossAxisCell where
  shape : StatementShape
  game  : PatternGame
  deriving Repr

/-- Cell + theorem-name witness.  Witness is a `String`; we do NOT
    prove anything about the cell — this is a catalog. -/
structure CrossAxisSpecimen where
  cell    : CrossAxisCell
  witness : String
  deriving Repr

/-! ## Specimens — one per occupied cell (audit anchors from . -/

/-- F1 × Catamorphism — `K_squared` (quaternion fold = -1). -/
def specimen_F1_catamorphism : CrossAxisSpecimen :=
  { cell    := { shape := .atomicCheck, game := .catamorphism }
    witness := "K_squared" }

/-- F2 × Cohabitation — `cohabit_peano_depth` (Peano-2 ∧ depth-1
    on the same Raw `slash a b h`).  This is the cross-cell that
    motivated the file. -/
def specimen_F2_cohabitation : CrossAxisSpecimen :=
  { cell    := { shape := .bundledChecks, game := .cohabitation }
    witness := "cohabit_peano_depth" }

/-- F3 × Dynamical — `pellFSMmod11_run_period_5` (∀ k, FSM cycles). -/
def specimen_F3_dynamical : CrossAxisSpecimen :=
  { cell    := { shape := .universal, game := .dynamical }
    witness := "pellFSMmod11_run_period_5" }

/-- F4 × Locality — `Raw.swap_depth` (term-mode lift, pointwise). -/
def specimen_F4_locality : CrossAxisSpecimen :=
  { cell    := { shape := .implication, game := .locality }
    witness := "Raw.swap_depth" }

/-- F5 × Typeclass — `image_contains_a` (∃ Raw producing the
    typeclass-distinguished element). -/
def specimen_F5_typeclass : CrossAxisSpecimen :=
  { cell    := { shape := .existential, game := .typeclass }
    witness := "image_contains_a" }

/-- F2 × ForcedOp — `atomic_iff_five` (Iff = ∧ of fwd+back).  After
    the H2 self-correction, `ForcedUniq` is the operator `Forced T`. -/
def specimen_F2_forcedUniq : CrossAxisSpecimen :=
  { cell    := { shape := .bundledChecks, game := .forcedOp }
    witness := "atomic_iff_five" }

/-- F6 × Typeclass — `int_image_strict` (¬∃ Raw mapping to negative
    Int — typeclass-image gap). -/
def specimen_F6_typeclass : CrossAxisSpecimen :=
  { cell    := { shape := .negativeExist, game := .typeclass }
    witness := "int_image_strict" }

/-! ## Extended specimens — H2 composites mapped to the audit's cells -/

/-- F2 × Lens — `succ_zero_view ∧ one_plus_one_view` style: bundles
    Lens-view equalities. -/
def specimen_F2_lens : CrossAxisSpecimen :=
  { cell    := { shape := .bundledChecks, game := .lens }
    witness := "succ_zero_view_bundle" }

/-- F3 × Catamorphism — `getBase_eq` (∀ x h, x = .object (getBase x h)). -/
def specimen_F3_catamorphism : CrossAxisSpecimen :=
  { cell    := { shape := .universal, game := .catamorphism }
    witness := "getBase_eq" }

/-- F2 × DynamicalAggregate — `pisano_predict_realises_pell_N`. -/
def specimen_F2_dynamicalAggregate : CrossAxisSpecimen :=
  { cell    := { shape := .bundledChecks, game := .dynamicalAggregate }
    witness := "pisano_predict_realises_pell_N" }

/-- F2 × LocalityAggregate — `polynomial_mvt_unitBracket_capstone_pure`. -/
def specimen_F2_localityAggregate : CrossAxisSpecimen :=
  { cell    := { shape := .bundledChecks, game := .localityAggregate }
    witness := "polynomial_mvt_unitBracket_capstone_pure" }

/-- F3 × CataForcedForm — `getBase_eq` viewed as form-level forcing. -/
def specimen_F3_cataForcedForm : CrossAxisSpecimen :=
  { cell    := { shape := .universal, game := .cataForcedForm }
    witness := "getBase_eq (form-level reading)" }

/-- F1 × Lens — `Lens.leaves.view Raw.a = 1` (atomic Lens evaluation). -/
def specimen_F1_lens : CrossAxisSpecimen :=
  { cell    := { shape := .atomicCheck, game := .lens }
    witness := "Lens.leaves_view_a" }

/-! ## Coverage observation

The cross-axis is **bias-saturated**: most theorems live in
F1-Atomic / F2-Aggregation columns, with F3 (universal) carrying
the catamorphism + dynamical content.  F4–F6 are sparse, populated
mainly by typeclass-image and reductio-style proofs.

Of the 6 × 21 = 126 cross-cells, this file names **exactly 13**
specimens (counting `def specimen_*` declarations).  Canonical
lower-bound encoded in `PatternCatalogSpan.occupiedCellLowerBound :
Nat := 13`.  The sparsity (~10%) confirms the catalog is well-
aligned with the actual theorem distribution: the non-empty cells
are the ones the codebase *naturally* uses, not the full Cartesian
product. -/

/-! ## Observation

The 13 specimens occupy 13 distinct cells out of 6 × 21 = 126.
The corpus populates the cross-axis sparsely: F2 ∩ {Aggregation,
Cohabitation, Forced-Uniqueness} dominate the bundle column; F1 ∩
{Catamorphism, Locality, Dynamical} dominate the atomic column.
Most cells are empty — not forbidden, just unrequired so far.
A future sweep can record cell occupancy by extending this list. -/

end E213.Lib.Math.Foundations.PatternCatalog.CrossAxis
