import E213.Math.PatternCatalog
import E213.Math.AxiomSystems.CrossTheoryCohabit

/-!
# PatternCatalog — Cross-Axis (Statement-Shape × Design-Pattern)

The merge of branch `claude/beilinson-conjecture-port-hg4Jf` brought in
the G17–G29 empirical audit corpus.  Reading G24
(`research-notes/audit/G24_six_families.md`) reveals that the audit's
**six functional families** classify theorems by *statement shape*,
while `PatternCatalog.lean`'s **six atomic games + 1 composite**
classify theorems by *codebase design pattern*.  These axes are
**orthogonal**.

## Concrete cross-cell evidence

G24 §2 F2c cites verbatim the same theorem `cohabit_peano_depth`
that powers `peanoDepthCohabit : CohabitationWitness Raw Nat Nat` in
`PatternCatalogInstance.lean`.  That single theorem occupies cell
**F2 (bundled checks) × Cohabitation**.  No contradiction — the two
classifications see the same theorem from different angles.
-/

namespace E213.Math.PatternCatalogCrossAxis

open E213.Math.PatternCatalog

/-- **Statement-shape axis** (audit corpus G24 §2): the functional
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

/-- **Design-pattern axis** (PatternCatalog 6 atomic + 1 composite). -/
inductive PatternGame where
  | locality
  | aggregation
  | typeclass
  | catamorphism
  | dynamical
  | forcedUniq
  | cohabitation
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

/-! ## Specimens — one per occupied cell (audit anchors from G24 §8). -/

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

/-- F2 × Forced-Uniqueness — `atomic_iff_five` (Iff = ∧ of fwd+back). -/
def specimen_F2_forcedUniq : CrossAxisSpecimen :=
  { cell    := { shape := .bundledChecks, game := .forcedUniq }
    witness := "atomic_iff_five" }

/-- F6 × Typeclass — `int_image_strict` (¬∃ Raw mapping to negative
    Int — typeclass-image gap). -/
def specimen_F6_typeclass : CrossAxisSpecimen :=
  { cell    := { shape := .negativeExist, game := .typeclass }
    witness := "int_image_strict" }

/-! ## Observation

Seven specimens occupy seven cells out of 6 × 7 = 42.  The corpus
populates the cross-axis sparsely: F2 ∩ {Aggregation, Cohabitation,
Forced-Uniqueness} dominate the bundle column; F1 ∩ {Catamorphism,
Locality, Dynamical} dominate the atomic column.  Most cells are
empty — not forbidden, just unrequired so far.  A future sweep can
record cell occupancy by extending this list. -/

end E213.Math.PatternCatalogCrossAxis
