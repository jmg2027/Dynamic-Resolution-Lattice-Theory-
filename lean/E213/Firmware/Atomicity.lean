import E213.Firmware.Atomicity.Five
import E213.Firmware.Atomicity.FiveHelpers
import E213.Firmware.Atomicity.PairForcing
import E213.Firmware.Atomicity.NonDecomposable
import E213.Firmware.Atomicity.ArityForcing
import E213.Firmware.Atomicity.ArityForcingGeneral
import E213.Firmware.Atomicity.PrimitiveSizes
import E213.Firmware.Atomicity.Alive

/-!
# Firmware: Atomicity API (re-export shim)

G12 D2: single-import entry point for the Atomicity sub-cluster's
public API.  Pattern mirrors `Firmware/Raw.lean` (Phase D shim).

Downstream code can `import E213.Firmware.Atomicity` and access
the **forced shape uniqueness** API in one line.

**Public API (FW-B in G12 §3.1 classification):**

  - `Five.{atomic_iff_five, canonical_partition, IsAlive}` —
    Δ⁴ atomicity: any abstract atomic structure with the right
    conditions must instantiate as d=5
  - `PairForcing.pair_iff_two` — pair size forced to 2
  - `NonDecomposable.closure_iff_three` — closure size forced to 3
  - `ArityForcing.arity_iff_two`,
    `ArityForcingGeneral.arity_iff_two` — k=2 arity forced
  - `PrimitiveSizes.{pairSize, closureSize}` — explicit sizes
  - `Alive.alive_iff_*` — alive-cell positions (1, 1) forced
  - `FiveHelpers.{add_two_ne_self, bezout_left, bezout_right}` —
    supporting Nat lemmas

**Role**: this is the axiom's *spec compliance* layer.  Together
with `Firmware/Raw.lean` (axiom data: Raw type + slash + slash_comm),
they form the dual character of the Firmware API:
  - Raw provides the axiom data
  - Atomicity provides the proof that this data is *the* unique
    minimal atomic structure (NOT a choice — forced)

**Imports**: pure-ℕ proofs; do NOT import `Raw` (deliberate
separation — these are abstract structural forcing arguments
that apply to any atomic system, then specialized to Raw).

**Axiom status**: ≤ {propext, Quot.sound} (some omega calls
remain in transitional status; migration to `omega213` is on the
backlog per CLAUDE.md `## DRLT Axiom Standard → Migration backlog`).

See `research-notes/G12_layered_api_classification.md` §3 for
the rigorous public-API classification.
-/
