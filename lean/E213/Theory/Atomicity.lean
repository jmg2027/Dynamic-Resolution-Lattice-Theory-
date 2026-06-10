import E213.Theory.Atomicity.Five
import E213.Theory.Atomicity.FiveHelpers
import E213.Theory.Atomicity.PairForcing
import E213.Theory.Atomicity.NonDecomposable
import E213.Theory.Atomicity.ArityForcing
import E213.Theory.Atomicity.PrimitiveSizes
import E213.Theory.Atomicity.Alive
import E213.Theory.Atomicity.OrbitForcing
import E213.Theory.Atomicity.CombinatorialArity

/-!
# Theory.Atomicity: forced shape-uniqueness API (re-export shim)

Single-import entry point for the Atomicity sub-cluster.
Downstream code can `import E213.Theory.Atomicity` and access
the **forced shape uniqueness** API in one line.

**Public API:**

  - `Five.{atomic_iff_five, canonical_partition, IsAlive}` —
    Δ⁴ atomicity: any abstract atomic structure with the right
    conditions must instantiate as d=5
  - `PairForcing.pair_iff_two` — pair size forced to 2
  - `NonDecomposable.closure_iff_three` — closure size forced to 3
  - `ArityForcing.arity_iff_two` — k=2 arity forced (Theory ring)
  - `Lib.Math.ArityForcingGeneral.arity_iff_two` — generalised
    `N < k` pigeonhole arity-forcing (Lib ring, uses Pigeonhole)
  - `PrimitiveSizes.{pairSize, closureSize}` — explicit sizes
  - `Alive.alive_iff_*` — alive-cell positions (1, 1) forced
  - `FiveHelpers.{add_two_ne_self, bezout_left, bezout_right}` —
    supporting Nat lemmas
  - `OrbitForcing.{canonical_solution, orbit_forcing_master}` —
    Pell-Lucas recurrence coefficients `(NS, det) = (3, 1)` forced
    by atomic seeds + target `L(2) = 7` (lifts static shape forcing
    to dynamic orbit forcing)

**Role**: the axiom's *spec compliance* layer.  Together with
`Theory/Raw.lean` (axiom data: Raw type + slash + slash_comm),
the two form the dual character of the Theory API:
  - Raw provides the axiom data
  - Atomicity provides the proof that this data is *the* unique
    minimal atomic structure (NOT a choice — forced)

**Imports**: pure-ℕ proofs; do NOT import `Raw` (deliberate
separation — these are abstract structural forcing arguments
that apply to any atomic system, then specialized to Raw).
-/
